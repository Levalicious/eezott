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
/* iterative (the memory layer's stacks): an item is a type to take the universe of, a binder's codomain to instantiate
   and take, or the maximum of the two results below it; in the recursion's order (the domain's subtree, then the
   codomain's), so every forcing happens as it did */
typedef struct { int k, depth, hasd; Val *v, *x; Val **tys; } VuItem;   /* k: 0 a type, 1 a codomain (v the binder, x its variable), 2 a maximum */
static Stack vust = { NULL, 0, 0, sizeof(VuItem) }, vures = { NULL, 0, 0, sizeof(LVal) };
static int val_universe(int depth0, Val *v0, Val **tys0, LVal *out) {
    size_t ib = vust.n, rb = vures.n;
    VuItem it0 = { 0, depth0, 0, v0, NULL, tys0 }; STACK_PUSH(&vust, VuItem, it0);
    while (vust.n > ib) {
        VuItem it = STACK_POP(&vust, VuItem);
        int depth = it.depth; Val **tys = it.tys; Val *v; LVal r;
        if (it.k == 2) {
            LVal lc = STACK_POP(&vures, LVal);
            if (it.hasd) { LVal ld = STACK_POP(&vures, LVal); lc = lv_max(ld, lc); }
            STACK_PUSH(&vures, LVal, lc); continue;
        }
        v = it.k == 1 ? inst(&it.v->clo, it.x) : it.v;
        v = force(v);
        switch (v->k) {
        case V_U: r = lv_add(v->lvl, 1); break;
        case V_PI: case V_SIGMA: {
            Val *dom = force(v->dom); int hasd = v->k == V_SIGMA || (dom->k != V_INTERVAL && dom->k != V_LEVEL);
            Val **t2 = xalloc((depth + 2) * sizeof(Val *)); for (int i = 0; i < depth; i++) t2[i] = tys ? tys[i] : NULL; t2[depth] = dom;
            Val *x = dom->k == V_INTERVAL ? vivar(depth) : dom->k == V_LEVEL ? vlvar(depth) : vvar(depth);
            VuItem mx = { 2, depth, hasd, NULL, NULL, NULL }; STACK_PUSH(&vust, VuItem, mx);
            VuItem cod = { 1, depth + 1, 0, v, x, t2 }; STACK_PUSH(&vust, VuItem, cod);
            if (hasd) { VuItem d = { 0, depth, 0, dom, NULL, tys }; STACK_PUSH(&vust, VuItem, d); }
            continue; }
        case V_PATHP: { VuItem n = { 0, depth, 0, vapp(v->a, vi(iv_zero()), 0), NULL, tys }; STACK_PUSH(&vust, VuItem, n); continue; }
        case V_PARTIAL: { VuItem n = { 0, depth, 0, v->b, NULL, tys }; STACK_PUSH(&vust, VuItem, n); continue; }
        case V_SUB: { VuItem n = { 0, depth, 0, v->a, NULL, tys }; STACK_PUSH(&vust, VuItem, n); continue; }
        case V_GLUE: r = v->lvl; break;
        case V_DATA: r = data_at(v->n, v->lvl)->lvl; break;
        case V_NEU: {
            int ok = 0;
            switch (v->h) {
            case H_VAR: ok = !(v->n < 0 || v->n >= depth || !tys || !tys[v->n]) && peel_universe(depth, tys[v->n], &v->args, tys, &r); break;
            case H_DEF: ok = peel_universe(depth, def_ty_at(v->n, v->lvl), &v->args, tys, &r); break;
            case H_TRANSP: { if (v->args.n) break; Val *T = force(vapp(v->a, vi(iv_one()), 0)); if (T->k != V_U) break; r = T->lvl; ok = 1; break; }
            case H_HCOMP: case H_OUTS: case H_UNGLUE: { if (v->args.n) break; Val *T = force(v->a); if (T->k != V_U) break; r = T->lvl; ok = 1; break; }
            default: break;
            }
            if (!ok) goto fail;
            break; }
        default: goto fail;
        }
        STACK_PUSH(&vures, LVal, r);
    }
    *out = STACK_POP(&vures, LVal);
    return 1;
fail:
    vust.n = ib; vures.n = rb; return 0;
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
/* one spine argument, already forced, against the pattern rules (pattern_spine's body): 0 if the spine is not a pattern */
int meta_pattern_arg(Val *m, int i, Val *x, int *lv, int *isi) {
    int ctxn = tmetas[m->n].ctxn;
    Arg *a = &m->args.a[i];
    if (a->proj || a->papp) return 0;
    int l, ii = 0;
    if (x->k == V_NEU && x->h == H_VAR && x->args.n == 0) l = x->n;
    else if (x->k == V_I && x->iv.n == 1 && x->iv.c[0].n == 1 && !x->iv.c[0].l[0].neg) { l = x->iv.c[0].l[0].var; ii = 1; }
    else if (x->k == V_L && x->lvl.c == 0 && x->lvl.n == 1 && x->lvl.t[0].off == 0 && !x->lvl.t[0].meta) l = x->lvl.t[0].var;
    else if (i < ctxn) { l = -2 - i; ii = x->k == V_I; }   /* a context position that is not a variable: ignorable */
    else return 0;                                          /* an application to a term: not a pattern */
    for (int j = 0; j < i; j++) if (lv[j] == l) return 0;
    lv[i] = l; isi[i] = ii;
    return 1;
}
typedef struct { int *lv, k, depth, id, occurs, scope; } Ren;
static Term *ren_vars(Term *t, Ren *r, int d);
static Term *copy_term(Term *t) { Term *r = xalloc(sizeof *r); *r = *t; return r; }
/* ren_vars the free variables of a term quoted at depth to the spine's binders; t is under d binders of its own */
/* the meta walks' node: a copy of the node with its walked children (a binder former's own slots; a system's branches) */
static Term *copy_build(Term *t, Term **k, void *ctx) {
    Term *c = copy_term(t); (void)ctx;
    if (t->k == T_SYS) {
        c->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { c->br[i].face = k[2 * i]; c->br[i].body = k[2 * i + 1]; }
        return c;
    }
    int n = term_nkids(t, 0);
    c->a = k[0]; if (n > 1) c->b = k[1]; if (n > 2) c->c = k[2]; if (n > 3) c->d = k[3];
    return c;
}
static int ren_vars_pre(Term *t, int d, void *ctx, TWDecide *o) {
    Ren *r = ctx;
    switch (t->k) {
    case T_VAR:
        o->r = t;
        if (t->n < d) return TW_DONE;
        { int level = r->depth - 1 - (t->n - d);
          for (int j = 0; j < r->k; j++) if (r->lv[j] == level) { o->r = mk_var(d + (r->k - 1 - j)); return TW_DONE; }
          r->scope = 1; return TW_DONE; }
    case T_META: if (t->n == r->id) r->occurs = 1; o->r = t; return TW_DONE;
    default: return TW_NODE;
    }
}
static Term *ren_vars(Term *t, Ren *r, int d) { return term_walk(t, d, 0, ren_vars_pre, copy_build, r); }
/* the solution: the body abstracted over the spine's binders */
Term *meta_solution_term(Term *body, int k, int *isi) {
    for (int j = k - 1; j >= 0; j--) { Term *l = mk_lam(xsprintf("x%d", j), body, 0); l->isi = isi[j]; body = l; }
    return body;
}
void meta_record(int id, Term *solt, Val *sol) {
    tmetas[id].solt = solt; tmetas[id].sol = sol;
    metas_version++;
    if (nundo == ucap) { ucap = ucap ? 2 * ucap : 64; undo = rrealloc(undo, ucap * sizeof(int)); }
    undo[nundo++] = id;
}
static void solve(int id, Term *body, int k, int *isi) {
    Term *solt = meta_solution_term(body, k, isi);
    meta_record(id, solt, eval(NULL, solt));
}
/* the quoted other side renamed to the spine's binders: *occurs if the meta occurs, *scope if a variable is outside the spine */
Term *meta_rename(Term *body, int *lv, int k, int depth, int id, int *occurs, int *scope) {
    Ren r = { lv, k, depth, id, 0, 0 };
    body = ren_vars(body, &r, 0);
    *occurs = r.occurs; *scope = r.scope;
    return body;
}
/* Miller pattern unification: the spine must be a pattern (see pattern_spine), the other side is quoted and its free variables renamed to
   the spine's binders; the meta occurring in it is refused, a free variable outside the spine postpones the constraint; anything that is
   not a pattern is postponed. The solution is then the most general one. */
/* unify_meta is the machine's (eval.c) */
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
static int mentions_meta_pre(Term *t, int d, void *ctx) { (void)d; return t->k == T_META ? (t->n == *(int *)ctx ? 1 : -1) : 0; }
int term_mentions_meta(Term *t, int id) { return term_any(t, 0, 1, mentions_meta_pre, &id); }
/* substitute an open term v for the variable idx (v lives in the context outside t's own binders) */
typedef struct { int idx; Term *v; } SubstO;
static int subst_open_pre(Term *t, int d, void *ctx, TWDecide *o) {
    SubstO *s = ctx;
    if (t->k != T_VAR) return TW_NODE;
    o->r = t->n == s->idx + d ? shift(s->v, 0, d) : t->n > s->idx + d ? mk_var(t->n - 1) : t;
    return TW_DONE;
}
static Term *subst_open(Term *t, int idx, Term *v, int d) { SubstO s = { idx, v }; return term_walk(t, d, 0, subst_open_pre, copy_build, &s); }
/* replace every meta by its solution applied to its spine (beta-reduced by substitution), structurally */
/* a solved meta's application: its spine arguments are zonked (outermost first), then the solution applied to them is
   zonked in its place */
static Term *zonk_post(Term *t, Term **rs, int n, void *ctx, void *aux) {
    Term *h = t; (void)ctx; (void)aux;
    while (h->k == T_APP) h = h->a;
    Meta *m = &tmetas[h->n];
    Term **args = xalloc((n + 1) * sizeof(Term *));
    for (int i = 0; i < n; i++) args[i] = rs[n - 1 - i];
    Term *body = m->solt; int k = 0;
    while (k < n && body->k == T_LAM) { body = body->a; k++; }
    /* innermost binder first; a spine term substituted while j binders remain outside is shifted past them */
    for (int j = k - 1; j >= 0; j--) body = subst_open(body, 0, shift(args[j], 0, j), 0);
    for (int j = k; j < n; j++) body = mk_app(body, args[j], 0);
    return body;
}
static int zonk_pre(Term *t, int d, void *ctx, TWDecide *o) {
    (void)d; (void)ctx;
    if (t->k == T_APP || t->k == T_META) {
        Term *h = t; int n = 0;
        while (h->k == T_APP) { n++; h = h->a; }
        if (h->k == T_META) {
            Meta *m = &tmetas[h->n];
            if (!m->sol) die("line %d: the implicit argument ?%d could not be inferred; write it, f {e} ..", m->line, h->n);
            o->ks = xalloc((n + 1) * sizeof(Term *)); o->nk = n; o->post = zonk_post;
            Term *w = t; for (int i = 0; i < n; i++) { o->ks[i] = w->b; w = w->a; }
            return TW_SPINE;
        }
    }
    if (t->k != T_SYS && !t->a && !t->b && !t->c && !t->d) { o->r = t; return TW_DONE; }
    return TW_NODE;
}
static Term *zonk_build(Term *t, Term **k, void *ctx) {
    Term *r = copy_term(t); (void)ctx;
    if (t->k == T_SYS) {
        r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = k[2 * i]; r->br[i].body = k[2 * i + 1]; }
        return r;
    }
    r->a = k[0]; r->b = k[1]; r->c = k[2]; r->d = k[3]; return r;
}
Term *zonk(Term *t) { return term_walk(t, 0, 1, zonk_pre, zonk_build, NULL); }
