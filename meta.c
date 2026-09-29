/*
 * meta.c - metavariables and unification, for implicit arguments and holes.
 *
 * A meta ?m is minted in a context of n variables and stands for a term
 * under those binders; its occurrences are the neutral ?m x_0 .. x_{n-1}
 * applied to the context's variables (oldest first). Conversion solves a
 * meta by pattern unification (Miller): when its spine is a list of distinct
 * variables the other side is quoted, its free variables are renamed to the
 * spine's binders, and the solution is the closed abstraction over the
 * spine. A free variable that is not in the spine postpones the constraint
 * (it may become solvable once other tmetas are solved); the meta occurring
 * in its own solution refuses it. A spine that is not a pattern (a variable
 * restricted to an endpoint by a face, a projection, a compound term)
 * postpones the constraint as well. Postponed constraints are retried when
 * the declaration ends, when every meta must be solved; the solutions are
 * then substituted structurally into the declaration's terms (zonk), never
 * by normalizing them.
 * Solutions are transactional with conversion: those found by a comparison
 * that fails are undone together with the level constraints it added.
 */
#include "tt.h"

Meta *tmetas; int ntmetas; static int mcap;
typedef struct { int depth; Val *a, *b; } Post;
static Post *posts; static int nposts, pcap;
static int *undo; static int nundo, ucap;

int meta_new(Val *ty, int ctxn, const char **names, Val **tys, int line) {
    if (ntmetas == mcap) { mcap = mcap ? 2 * mcap : 64; tmetas = rrealloc(tmetas, mcap * sizeof(Meta)); }
    Meta *m = &tmetas[ntmetas]; memset(m, 0, sizeof *m);
    m->ty = ty; m->ctxn = ctxn; m->line = line;
    m->names = xalloc((ctxn + 1) * sizeof(char *)); m->tys = xalloc((ctxn + 1) * sizeof(Val *));
    for (int i = 0; i < ctxn; i++) { m->names[i] = names[i]; m->tys[i] = tys ? tys[i] : NULL; }
    return ntmetas++;
}

/* ---- the universe of a type value (M20): l with ty : U l, when the value's shape determines it ---- */
static int val_universe(int depth, Val *v, Val **tys, LVal *out);
/* the type of a head applied along a spine, which must end in a universe */
static int peel_universe(int depth, Val *ty, VList *args, Val **tys, LVal *out) {
    for (int i = 0; i < args->n; i++) {
        Arg *a = &args->a[i]; ty = force(ty);
        if (a->proj) return 0;
        if (a->papp) { if (ty->k != V_PATHP) return 0; ty = vapp(ty->a, a->v, 0); continue; }
        if (ty->k != V_PI) return 0;
        ty = inst(&ty->clo, a->v);
    }
    ty = force(ty);
    if (ty->k != V_U) return 0;
    *out = ty->lvl; return 1;
}
static int val_universe(int depth, Val *v, Val **tys, LVal *out) {
    v = force(v);
    switch (v->k) {
    case V_U: *out = lv_add(v->lvl, 1); return 1;
    case V_PI: case V_SIGMA: {
        Val *dom = force(v->dom); LVal ld, lc; int hasd = 0;
        if (v->k == V_SIGMA || (dom->k != V_INTERVAL && dom->k != V_LEVEL)) { if (!val_universe(depth, dom, tys, &ld)) return 0; hasd = 1; }
        Val **t2 = xalloc((depth + 2) * sizeof(Val *)); for (int i = 0; i < depth; i++) t2[i] = tys ? tys[i] : NULL; t2[depth] = dom;
        Val *x = dom->k == V_INTERVAL ? vivar(depth) : dom->k == V_LEVEL ? vlvar(depth) : vvar(depth);
        if (!val_universe(depth + 1, inst(&v->clo, x), t2, &lc)) return 0;
        *out = hasd ? lv_max(ld, lc) : lc; return 1; }
    case V_PATHP: return val_universe(depth, vapp(v->a, vi(iv_zero()), 0), tys, out);
    case V_PARTIAL: return val_universe(depth, v->b, tys, out);
    case V_SUB: return val_universe(depth, v->a, tys, out);
    case V_GLUE: *out = v->lvl; return 1;
    case V_DATA: *out = data_at(v->n, v->lvl)->lvl; return 1;
    case V_NEU:
        switch (v->h) {
        case H_VAR: if (v->n < 0 || v->n >= depth || !tys || !tys[v->n]) return 0; return peel_universe(depth, tys[v->n], &v->args, tys, out);
        case H_DEF: return peel_universe(depth, def_ty_at(v->n, v->lvl), &v->args, tys, out);
        case H_TRANSP: { if (v->args.n) return 0; Val *T = force(vapp(v->a, vi(iv_one()), 0)); if (T->k != V_U) return 0; *out = T->lvl; return 1; }
        case H_HCOMP: case H_OUTS: case H_UNGLUE: { if (v->args.n) return 0; Val *T = force(v->a); if (T->k != V_U) return 0; *out = T->lvl; return 1; }
        default: return 0;
        }
    default: return 0;
    }
}
/* ?id applied to the context's variables, oldest first: ?id #(n-1) .. #0 */
Term *meta_term(int id, int ctxn) {
    Term *t = mk_term(T_META, NULL, NULL, NULL, NULL); t->n = id;
    for (int i = ctxn - 1; i >= 0; i--) t = mk_app(t, mk_var(i), 0);
    return t;
}
int metas_version;   /* see tt.h: the memo on a rigid definition application is valid only at the version it was taken at */
int force_depth;
/* fmeta and force are the machine's (eval.c) */
MMark meta_mark(void) { MMark m = { nundo, nposts }; return m; }
void meta_rollback(MMark m) {
    while (nundo > m.u) { int id = undo[--nundo]; tmetas[id].sol = NULL; tmetas[id].solt = NULL; }
    metas_version++;
    if (nposts > m.p) nposts = m.p;
}
void meta_postpone(int depth, Val *a, Val *b) {
    if (nposts == pcap) { pcap = pcap ? 2 * pcap : 16; posts = rrealloc(posts, pcap * sizeof(Post)); }
    posts[nposts].depth = depth; posts[nposts].a = a; posts[nposts].b = b; nposts++;
}

/* the spine as a pattern: the de Bruijn levels of its variables in lv[] (distinct: a repeated variable is not a pattern), whether
   each is an interval variable in isi[]. An entry that is not a variable (a let-bound variable's value, an interval variable the
   context restricted to an endpoint, any other term) is an ignorable position: the solution may not use it, which is sound (it
   is a solution) and incomplete only when the other side needs it, in which case a free variable is out of scope and the
   constraint is postponed. */
static int pattern_spine(Val *m, int *lv, int *isi) {
    int ctxn = tmetas[m->n].ctxn;   /* the first ctxn entries are the meta's context; the rest are applications of the meta */
    for (int i = 0; i < m->args.n; i++) {
        Arg *a = &m->args.a[i];
        if (a->proj || a->papp) return 0;
        Val *x = force(a->v); int l, ii = 0;
        if (x->k == V_NEU && x->h == H_VAR && x->args.n == 0) l = x->n;
        else if (x->k == V_I && x->iv.n == 1 && x->iv.c[0].n == 1 && !x->iv.c[0].l[0].neg) { l = x->iv.c[0].l[0].var; ii = 1; }
        else if (x->k == V_L && x->lvl.c == 0 && x->lvl.n == 1 && x->lvl.t[0].off == 0 && !x->lvl.t[0].meta) l = x->lvl.t[0].var;
        else if (i < ctxn) { l = -2 - i; ii = x->k == V_I; }   /* a context position that is not a variable: ignorable */
        else return 0;                                          /* an application to a term: not a pattern */
        for (int j = 0; j < i; j++) if (lv[j] == l) return 0;
        lv[i] = l; isi[i] = ii;
    }
    return 1;
}
typedef struct { int *lv, k, depth, id, occurs, scope; } Ren;
static Term *copy_term(Term *t) { Term *r = xalloc(sizeof *r); *r = *t; return r; }
/* ren_vars the free variables of a term quoted at depth to the spine's binders; t is under d binders of its own */
static Term *ren_vars(Term *t, Ren *r, int d) {
    if (!t) return NULL;
    Term *c;
    switch (t->k) {
    case T_VAR:
        if (t->n < d) return t;
        { int level = r->depth - 1 - (t->n - d);
          for (int j = 0; j < r->k; j++) if (r->lv[j] == level) return mk_var(d + (r->k - 1 - j));
          r->scope = 1; return t; }
    case T_META: if (t->n == r->id) r->occurs = 1; return t;
    case T_PI: case T_SIGMA: c = copy_term(t); c->a = ren_vars(t->a, r, d); c->b = ren_vars(t->b, r, d + 1); return c;
    case T_LAM: c = copy_term(t); c->a = ren_vars(t->a, r, d + 1); return c;
    case T_LET: c = copy_term(t); c->a = ren_vars(t->a, r, d); c->b = ren_vars(t->b, r, d); c->c = ren_vars(t->c, r, d + 1); return c;
    case T_SYS:
        c = copy_term(t); c->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { c->br[i].face = ren_vars(t->br[i].face, r, d); c->br[i].body = ren_vars(t->br[i].body, r, d); }
        return c;
    default:
        c = copy_term(t); c->a = ren_vars(t->a, r, d); c->b = ren_vars(t->b, r, d); c->c = ren_vars(t->c, r, d); c->d = ren_vars(t->d, r, d); return c;
    }
}
static void solve(int id, Term *body, int k, int *isi) {
    for (int j = k - 1; j >= 0; j--) { Term *l = mk_lam(xsprintf("x%d", j), body, 0); l->isi = isi[j]; body = l; }
    tmetas[id].solt = body; tmetas[id].sol = eval(NULL, body);
    metas_version++;
    if (nundo == ucap) { ucap = ucap ? 2 * ucap : 64; undo = rrealloc(undo, ucap * sizeof(int)); }
    undo[nundo++] = id;
}
/* Miller pattern unification: the spine must be a pattern (see pattern_spine), the other side is quoted and its free variables renamed to
   the spine's binders; the meta occurring in it is refused, a free variable outside the spine postpones the constraint; anything that is
   not a pattern is postponed. The solution is then the most general one. */
int unify_meta(int depth, Val *m, Val *other) {
    int k = m->args.n; int *lv = xalloc((k + 1) * sizeof(int)), *isi = xalloc((k + 1) * sizeof(int));
    if (!pattern_spine(m, lv, isi)) { meta_postpone(depth, m, other); return 1; }
    Term *body = quote(depth, other);
    Ren r = { lv, k, depth, m->n, 0, 0 };
    body = ren_vars(body, &r, 0);
    if (r.occurs) return 0;
    if (r.scope) { meta_postpone(depth, m, other); return 3; }   /* 3: postponed for a variable out of the spine's scope */
    solve(m->n, body, k, isi);
    return 1;
}
void meta_drop_last_post(void) { if (nposts > 0) nposts--; }

static const char *vshow(int depth, Val *v, const char **names, int nnames) {
    char *buf = NULL; size_t sz = 0; FILE *f = open_memstream(&buf, &sz);
    const char **nm = xalloc((depth + 256) * sizeof(char *));
    for (int i = 0; i < depth && i < nnames; i++) nm[i] = names[i];
    term_print(f, quote(depth, v), nm, depth);
    fclose(f); return buf;
}
/* at the end of a declaration: retry the postponed constraints until no more are solved, then every meta minted since m0 must be solved */
void metas_finish(const char *what, int line, int m0) {
    for (;;) {
        int n = nposts; if (n == 0) break;
        Post *ps = xalloc((n + 1) * sizeof(Post)); memcpy(ps, posts, n * sizeof(Post)); nposts = 0;
        for (int i = 0; i < n; i++)
            if (!conv(ps[i].depth, ps[i].a, ps[i].b))
                die("line %d: in %s, a postponed constraint fails: %s is not %s", line, what, vshow(ps[i].depth, ps[i].a, NULL, 0), vshow(ps[i].depth, ps[i].b, NULL, 0));
        if (nposts >= n) {   /* nothing solved: the remaining constraints are not determined */
            Post *p = &posts[0];
            die("line %d: in %s, the constraint %s = %s cannot be solved: an implicit argument is not determined here (a variable not in scope, or a face restriction); write it, f {e} ..",
                line, what, vshow(p->depth, p->a, NULL, 0), vshow(p->depth, p->b, NULL, 0));
        }
    }
    for (int id = m0; id < ntmetas; id++) if (!tmetas[id].sol && !tmetas[id].deferred) {
        Meta *m = &tmetas[id];
        die("line %d: in %s, the implicit argument ?%d (line %d, of type %s) could not be inferred; write it, f {e} ..", line, what, id, m->line, vshow(m->ctxn, m->ty, m->names, m->ctxn));
    }
    /* M20: a meta standing for a type lives in a universe U l; its solution must lie in it - the level constraint an explicit
       argument gets from check() (elab.c: got->lvl <= U->lvl). Without it K {A : U} (x : A) : U := A gives uu : U := K U, U : U. */
    for (int id = m0; id < ntmetas; id++) {
        Meta *m = &tmetas[id]; if (!m->sol) continue;
        Val *ty = force(m->ty); if (ty->k != V_U) continue;
        Val *s = m->sol;
        for (int i = 0; i < m->ctxn; i++) { Val *vt = m->tys[i] ? force(m->tys[i]) : NULL; s = vapp(s, vt && vt->k == V_INTERVAL ? vivar(i) : vt && vt->k == V_LEVEL ? vlvar(i) : vvar(i), 0); }
        LVal u;
        if (!val_universe(m->ctxn, s, m->tys, &u))   /* never happens on the corpus (0 of 140 programs); when it does, the level is not checked, so refuse rather than pass */
            die("line %d: in %s, the implicit argument ?%d (line %d) : %s is solved by %s, whose universe cannot be determined; write it, f {e} ..", line, what, id, m->line, vshow(m->ctxn, ty, m->names, m->ctxn), vshow(m->ctxn, s, m->names, m->ctxn));
        if (lv_enforce_leq(u, ty->lvl) != 1)
            die("line %d: in %s, universe inconsistency: the implicit argument ?%d (line %d) : %s is solved by %s, a type in %s", line, what, id, m->line,
                vshow(m->ctxn, ty, m->names, m->ctxn), vshow(m->ctxn, s, m->names, m->ctxn), vshow(m->ctxn, vu_l(u), m->names, m->ctxn));
    }
}

/* retry the postponed constraints until none is solved (the erasure's law matching): 1 if none remain, 0 if one fails or is undetermined */
int metas_retry(void) {
    for (;;) {
        int n = nposts; if (n == 0) return 1;
        Post *ps = xalloc((n + 1) * sizeof(Post)); memcpy(ps, posts, n * sizeof(Post)); nposts = 0;
        for (int i = 0; i < n; i++) if (!conv(ps[i].depth, ps[i].a, ps[i].b)) return 0;
        if (nposts >= n) return 0;
    }
}
int meta_solved(int id) { return tmetas[id].sol != NULL; }

/* assign a meta minted with the context as its spine the term t of that context: the solution abstracts the context's variables,
   under which t's indices are unchanged (binder j is the variable at level j) */
void meta_assign(int id, Term *t, int ctxn) {
    int *isi = xalloc((ctxn + 1) * sizeof(int));
    solve(id, t, ctxn, isi);
}
int term_mentions_meta(Term *t, int id) {
    if (!t) return 0;
    if (t->k == T_META) return t->n == id;
    if (t->k == T_SYS) { for (int i = 0; i < t->nbr; i++) if (term_mentions_meta(t->br[i].face, id) || term_mentions_meta(t->br[i].body, id)) return 1; return 0; }
    return term_mentions_meta(t->a, id) || term_mentions_meta(t->b, id) || term_mentions_meta(t->c, id) || term_mentions_meta(t->d, id);
}
/* substitute an open term v for the variable idx (v lives in the context outside t's own binders) */
static Term *subst_open(Term *t, int idx, Term *v, int d) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR: if (t->n == idx + d) return shift(v, 0, d); if (t->n > idx + d) return mk_var(t->n - 1); return t;
    case T_PI: case T_SIGMA: r = copy_term(t); r->a = subst_open(t->a, idx, v, d); r->b = subst_open(t->b, idx, v, d + 1); return r;
    case T_LAM: r = copy_term(t); r->a = subst_open(t->a, idx, v, d + 1); return r;
    case T_LET: r = copy_term(t); r->a = subst_open(t->a, idx, v, d); r->b = subst_open(t->b, idx, v, d); r->c = subst_open(t->c, idx, v, d + 1); return r;
    case T_SYS:
        r = copy_term(t); r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = subst_open(t->br[i].face, idx, v, d); r->br[i].body = subst_open(t->br[i].body, idx, v, d); }
        return r;
    default:
        r = copy_term(t); r->a = subst_open(t->a, idx, v, d); r->b = subst_open(t->b, idx, v, d); r->c = subst_open(t->c, idx, v, d); r->d = subst_open(t->d, idx, v, d); return r;
    }
}
/* replace every meta by its solution applied to its spine (beta-reduced by substitution), structurally */
Term *zonk(Term *t) {
    if (!t) return NULL;
    Term *r;
    if (t->k == T_APP || t->k == T_META) {
        Term *h = t; int n = 0;
        while (h->k == T_APP) { n++; h = h->a; }
        if (h->k == T_META) {
            Meta *m = &tmetas[h->n];
            if (!m->sol) die("line %d: the implicit argument ?%d could not be inferred; write it, f {e} ..", m->line, h->n);
            Term **args = xalloc((n + 1) * sizeof(Term *)); Term *w = t;
            for (int i = n - 1; i >= 0; i--) { args[i] = zonk(w->b); w = w->a; }
            Term *body = m->solt; int k = 0;
            while (k < n && body->k == T_LAM) { body = body->a; k++; }
            /* innermost binder first; a spine term substituted while j binders remain outside is shifted past them */
            for (int j = k - 1; j >= 0; j--) body = subst_open(body, 0, shift(args[j], 0, j), 0);
            for (int j = k; j < n; j++) body = mk_app(body, args[j], 0);
            return zonk(body);
        }
    }
    switch (t->k) {
    case T_SYS:
        r = copy_term(t); r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = zonk(t->br[i].face); r->br[i].body = zonk(t->br[i].body); }
        return r;
    default:
        if (!t->a && !t->b && !t->c && !t->d) return t;
        r = copy_term(t); r->a = zonk(t->a); r->b = zonk(t->b); r->c = zonk(t->c); r->d = zonk(t->d); return r;
    }
}
