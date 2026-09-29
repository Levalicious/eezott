/*
 * elab.c - bidirectional elaboration of surface terms into core terms.
 *
 * infer :: ctx -> surface -> (core, type value)
 * check :: ctx -> surface -> type value -> core
 *
 * Every binder and every application is marked with its computational
 * relevance: a binder whose type is a universe or a family into a universe
 * carries no data at run time, and erasure drops it.  Data declarations
 * are checked for strict positivity and predicativity; their induction
 * principles are synthesized as closed core types on demand.
 *
 * Cubical constructs: interval variables live in the context with the
 * pretype I; a path abstraction is checked against its line and then its
 * endpoints are compared under the faces i=0 and i=1; a system is checked
 * branch by branch in the context restricted to each branch's face, and the
 * branches are compared where their faces overlap; transp needs its line
 * constant on phi, hcomp needs its base to agree with its sides on phi.
 */
#include "tt.h"
#include "machine.h"

typedef struct { const char **names; Val **tys; int *irrs; int n, cap; Env *env; int abs; int irrpos, irrlen; } Ctx;
/* irrs[i]: variable i is irrelevant; irrpos > 0: irrelevant things may be used here (a type, an irrelevant argument or
   component); irrlen > 0: a conversion failure is not an error (the component is never inspected - Agda's convError
   suppression) - only the genuinely irrelevant term positions, never a type being checked */
/* irrpos > 0: the term being checked is in an irrelevant position (the argument of an irrelevant binder, the irrelevant component
   of a pair): the irrelevant component of a pair may be projected only there (M16a; Abel's rule - a type's relevant argument
   positions are not irrelevant positions) */
int word_type = -1, word_nat = -1;
int decl_seq;
static const char *wordop_names[] = { "wadd", "wsub", "wmul", "wand", "wor", "wxor", "wshl", "wshr", "weq", "wlt", "waddc", "wsubb", "wmull", "wdivmod" };
int wordop_code(const char *name) { for (int i = 0; i < 14; i++) if (!strcmp(name, wordop_names[i])) return i + 1; return 0; }
const char *wordop_name(int code) { return wordop_names[code - 1]; }
/* abs: the global being elaborated declares Level binders, so its constant levels are absolute (U is U 0);
   otherwise constants are relative to the hidden level L (U n is U {L + n}) */
#define BASE_LEVEL(c) ((c)->abs ? lv_const(0) : lv_hidden())

static void ctx_push(Ctx *c, const char *name, Val *ty, Val *val) {
    if (c->n == c->cap) {
        int cap = c->cap ? 2 * c->cap : 16;
        const char **nn = xalloc(cap * sizeof(char *)); Val **nt = xalloc(cap * sizeof(Val *)); int *ni = xalloc(cap * sizeof(int));
        if (c->n) { memcpy(nn, c->names, c->n * sizeof(char *)); memcpy(nt, c->tys, c->n * sizeof(Val *)); memcpy(ni, c->irrs, c->n * sizeof(int)); }
        c->names = nn; c->tys = nt; c->irrs = ni; c->cap = cap;
    }
    c->names[c->n] = name; c->tys[c->n] = ty; c->irrs[c->n] = 0; c->n++;
    c->env = env_push(c->env, val);
}
static void ctx_pop(Ctx *c) { c->n--; c->env = c->env->next; }
static void ctx_bind(Ctx *c, const char *name, Val *ty) { ctx_push(c, name, ty, ty->k == V_LEVEL ? vlvar(c->n) : vvar(c->n)); }
/* an irrelevant variable (the binder .(x : A)): usable only in irrelevant positions */
static void ctx_bind_irr(Ctx *c, const char *name, Val *ty, int irr) { ctx_bind(c, name, ty); if (irr & 2) c->irrs[c->n - 1] = 1; }
static void ctx_bind_i(Ctx *c, const char *name) { ctx_push(c, name, mkval(V_INTERVAL), vivar(c->n)); }
/* a fresh meta of a type, applied to the context: a level meta when the type is Level (solved by the level store) */
static Term *fresh_meta(Ctx *c, Val *ty, int line) {
    ty = force(ty);
    if (ty->k == V_LEVEL) { int m = lv_meta_new(); Term *t = mk_term(T_LMETA, NULL, NULL, NULL, NULL); t->n = m; return t; }
    return meta_term(meta_new(ty, c->n, c->names, c->tys, line), c->n);
}

/* the context restricted to a face: types and environment values re-evaluated with the face's endpoints */
static Ctx ctx_restrict(Ctx *c, const Face *f) {
    Ctx r = {0}; r.n = c->n; r.cap = c->n; r.irrs = c->irrs; r.irrpos = c->irrpos; r.irrlen = c->irrlen;   /* irrelevance is the same under a face */
    r.names = xalloc((c->n + 1) * sizeof(char *)); r.tys = xalloc((c->n + 1) * sizeof(Val *));
    Val **vs = xalloc((c->n + 1) * sizeof(Val *));
    for (int i = 0; i < c->n; i++) { r.names[i] = c->names[i]; r.tys[i] = restrict_val(c->tys[i], f); vs[c->n - 1 - i] = env_get(c->env, i); }
    for (int i = 0; i < c->n; i++) r.env = env_push(r.env, restrict_val(vs[i], f));
    return r;
}

static int cur_data = -1, cur_data_hi = -1;   /* the block of data types being declared, [cur_data, cur_data_hi): their occurrences are at the hidden level */
const char *cur_decl_name;   /* the declaration being elaborated, named by the literal-elimination tripwire */
#define IN_DECL(d) ((d) >= cur_data && (d) < cur_data_hi)
static int find_def(const char *n) { for (int i = ndefs - 1; i >= 0; i--) if (!strcmp(defs[i].name, n)) return i; return -1; }
static int find_data(const char *n) { for (int i = ndatas - 1; i >= 0; i--) if (!strcmp(datas[i].name, n)) return i; return -1; }
static int find_con(const char *n) { for (int i = ncons - 1; i >= 0; i--) if (!strcmp(cons[i].name, n)) return i; return -1; }
static void check_fresh(const char *n, int line) {
    if (find_def(n) >= 0 || find_data(n) >= 0 || find_con(n) >= 0) die("line %d: '%s' is already defined", line, n);
}

/* the most binders on any path through t (iterative: the memory layer's stack) */
typedef struct { Term *t; int above; } TBItem;
static Stack tbst = { NULL, 0, 0, sizeof(TBItem) };
static int term_binders(Term *t) {
    size_t base = tbst.n; int m = 0;
    TBItem it0 = { t, 0 }; STACK_PUSH(&tbst, TBItem, it0);
    while (tbst.n > base) {
        TBItem it = STACK_POP(&tbst, TBItem);
        if (!it.t) continue;
        Term *u = it.t; int here = it.above + (u->k == T_PI || u->k == T_LAM || u->k == T_LET || u->k == T_SIGMA);   /* a Sigma binds its codomain's variable too */
        if (here > m) m = here;
        Term *ks[4] = { u->a, u->b, u->c, u->d };
        for (int i = 0; i < 4; i++) { TBItem c = { ks[i], here }; STACK_PUSH(&tbst, TBItem, c); }
        for (int i = 0; i < u->nbr; i++) { TBItem f = { u->br[i].face, here }, b = { u->br[i].body, here }; STACK_PUSH(&tbst, TBItem, f); STACK_PUSH(&tbst, TBItem, b); }
    }
    return m;
}
static const char *show(Ctx *c, Val *v) {
    Term *t = quote(c->n, force(v));   /* messages show the canonical value: force unfolds rigid definition applications */
    const char **names = xalloc((c->n + term_binders(t) + 1) * sizeof(char *));
    if (c->n) memcpy(names, c->names, c->n * sizeof(char *));
    char *buf = NULL; size_t sz = 0; FILE *f = open_memstream(&buf, &sz);
    term_print(f, t, names, c->n); fclose(f);
    char *s = xstrdup(buf); free(buf); return s;
}
static void expect_conv(Ctx *c, int line, Val *got, Val *want, const char *what) {
    /* in an irrelevant position a conversion failure is not an error: the component is never used (Agda's
       convError suppression; the discipline the Word design's .() proofs rely on) */
    if (!conv(c->n, got, want) && !c->irrlen) die("line %d: %s has type %s, expected %s", line, what, show(c, got), show(c, want));
}

typedef struct { int depth, cod; Val *v; } TLItem;   /* cod: the codomain of the Sigma v, at depth */
static Stack tlst = { NULL, 0, 0, sizeof(TLItem) };
int is_type_like(int depth0, Val *ty0) {
    size_t base = tlst.n;
    TLItem it0 = { depth0, 0, ty0 }; STACK_PUSH(&tlst, TLItem, it0);
    while (tlst.n > base) {
        TLItem it = STACK_POP(&tlst, TLItem);
        int depth = it.depth; Val *ty = it.cod ? inst(&it.v->clo, vvar(depth - 1)) : it.v;
        for (;;) {
            ty = force(ty);
            if (ty->k == V_U || ty->k == V_LEVEL) break;
            if (ty->k == V_PI) { ty = inst(&ty->clo, ty->isi ? vivar(depth) : vvar(depth)); depth++; continue; }
            if (ty->k == V_PATHP) { ty = vapp(ty->a, vivar(depth), 0); depth++; continue; }
            if (ty->k == V_PARTIAL) { ty = ty->b; continue; }
            if (ty->k == V_SUB) { ty = ty->a; continue; }
            if (ty->k == V_SIGMA) { TLItem c = { depth + 1, 1, ty }; STACK_PUSH(&tlst, TLItem, c); ty = ty->dom; continue; }
            tlst.n = base; return 0;
        }
    }
    return 1;
}

static Term *check(Ctx *c, STerm *s, Val *ty);
static Term *check_type_sort(Ctx *c, STerm *s, LVal *lvl, int *pre);
static Term *check_type(Ctx *c, STerm *s, LVal *lvl);
static Term *check_interval(Ctx *c, STerm *s);
static void resolve_deferred(Ctx *c, int all);

/* a term must be a type of either sort: returns its core, universe level and whether it is a pretype */
/* a type whose sort is not known yet (a meta, e.g. an implicit parameter still to be inferred) is in a universe at a fresh level */
static Val *refine_to_universe(Ctx *c, Val *ty) {
    ty = force(ty);
    ty = force(ty);
    if (ty->k == V_NEU && ty->h == H_META) { int l = lv_meta_new(); if (conv(c->n, ty, vu_l(lv_meta(l)))) ty = force(ty); }
    return ty;
}
/* a term must be a type in a universe (with Kan structure): pretypes are refused */
/* a line of types  (i : I) -> U l : either a lambda over an interval variable, or a term whose type is such a function */
static Val *vinterval(void) { return mkval(V_INTERVAL); }

/* ---- induction principles ---- */

/* D p i, under a context where params start at index pbase (p_t = pbase + np-1-t) and indices at index ibase (i_j = ibase + m-1-j) */
static Term *elim_dlt;   /* the level of the data type while building an eliminator type */
static Term *data_applied(int d, int pbase, int ibase) {
    Data *D = &datas[d]; Term *t = mk_ref_l(T_DATA, d, elim_dlt);
    for (int i = 0; i < D->nparams; i++) t = mk_app(t, mk_var(pbase + D->nparams - 1 - i), 1);
    for (int j = 0; j < D->nidx; j++) t = mk_app(t, mk_var(ibase + D->nidx - 1 - j), 1);
    return t;
}

/* closed type of  elim D  for a motive into U lvl; res_irr says the motive's fibres are themselves types */

/* the boundary image E: a boundary term of constructor C (already shifted into the method's context) with recursive
   arguments replaced by their induction hypotheses and constructors by their methods.
   Context: [params, P, mth(ci), a(r), ih(htot), iv(n)] (+ depth under binders). */
typedef struct { Con *C; int n, r, htot, o, nb, pi, np; LVal dl; int *record; } EInfo;   /* o: C's ordinal in the block; nb: members; pi: C's member's position */
static Term *E(Term *t, EInfo *I, int depth);
static Term *boundary_at(Con *C, int end);

/* instantiate a term under a telescope of n binders (vs[0] the innermost) with terms of the outer context */
typedef struct { int n; Term **vs; } InstTele;
static int inst_tele_pre(Term *t, int k, void *ctx, TWDecide *o) {
    InstTele *it = ctx;
    switch (t->k) {
    case T_VAR:
        if (t->n < k) o->r = t;
        else if (t->n - k < it->n) o->r = shift(it->vs[t->n - k], 0, k);
        else o->r = mk_var(t->n - it->n);
        return TW_DONE;
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: o->r = t; return TW_DONE;
    default: return TW_NODE;
    }
}
static Term *inst_tele_build(Term *t, Term **q, void *ctx) {
    Term *r; (void)ctx;
    switch (t->k) {
    case T_PI:  r = mk_pi(t->name, q[0], q[1], t->irr); r->isi = t->isi; r->pre = t->pre; return r;
    case T_LAM: r = mk_lam(t->name, q[0], t->irr); r->isi = t->isi; return r;
    case T_SIGMA: r = mk_term(T_SIGMA, q[0], q[1], NULL, NULL); r->name = t->name; return r;
    case T_LET: return mk_let(t->name, q[0], q[1], q[2], t->irr);
    case T_SYS:
        r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = q[2 * i]; r->br[i].body = q[2 * i + 1]; }
        return r;
    default:
        r = mk_term(t->k, q[0], q[1], q[2], q[3]);
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; r->num = t->num; return r;
    }
}
/* instantiate a term under a telescope of n binders (vs[0] the innermost) with terms of the outer context */
Term *inst_tele(Term *t, int n, Term **vs, int k) { InstTele it = { n, vs }; return term_walk(t, k, 0, inst_tele_pre, inst_tele_build, &it); }
/* t = c' p.. a'.. is.. (a constructor of the same data type applied): the method applied (E_con_post), from the images of
   the terms E_con_pre lists: the recursive arguments, then the path method's endpoints, or the cube's boundary system
   followed by the indices that have images */
typedef struct { Con *Cp; Term **args, **vs; int nargs, np, tn, nrec, depth; } ECon;
static ECon *E_con_pre(Term *t, EInfo *I, int depth, Term ***ks, int *nk) {
    int nargs = 0; Term *w = t;
    while (w->k == T_APP) { nargs++; w = w->a; }
    if (w->k != T_CON || datas[cons[w->n].data].block != datas[I->C->data].block) return NULL;
    Con *Cp = con_at(w->n, I->dl); int np = I->np;
    if (Cp->data != I->C->data && Cp->nint > 0) die("the index of %s applies the path constructor %s of another member: not supported", I->C->name, Cp->name);
    if (Cp->bord >= I->o) die("the boundary of %s uses the later constructor %s; boundaries may only use earlier constructors", I->C->name, Cp->name);
    if (nargs != np + Cp->nargs + Cp->nint) die("internal: constructor %s applied to %d arguments in a boundary", Cp->name, nargs);
    ECon *e = xalloc(sizeof *e); e->Cp = Cp; e->nargs = nargs; e->np = np; e->depth = depth;
    Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
    for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    e->args = args;
    int cap = Cp->nargs + 3 + datas[Cp->data].nidx; Term **k = xalloc(cap * sizeof(Term *)); int n = 0;
    for (int j = 0; j < Cp->nargs; j++) if (Cp->args[j].isrec || Cp->args[j].isrecpath) k[n++] = args[np + j];
    e->nrec = n;
    if (Cp->nint > 0) {
        /* a path constructor: its own boundary, instantiated along the spine ([params, args]: vs[0] is the last argument) */
        int tn = np + Cp->nargs; Term **vs = xalloc((tn + Cp->nint + 1) * sizeof(Term *));
        for (int j = 0; j < Cp->nargs; j++) vs[j] = args[np + Cp->nargs - 1 - j];
        for (int i = 0; i < np; i++) vs[Cp->nargs + i] = args[np - 1 - i];
        e->vs = vs; e->tn = tn;
        if (Cp->pathmethod) {
            k[n++] = inst_tele(boundary_at(Cp, 0), tn, vs, 0);
            k[n++] = inst_tele(boundary_at(Cp, 1), tn, vs, 0);
        } else if (Cp->boundary) {
            Term **vs2 = xalloc((tn + Cp->nint + 1) * sizeof(Term *));
            for (int q = 0; q < Cp->nint; q++) vs2[q] = args[np + Cp->nargs + Cp->nint - 1 - q];
            for (int i = 0; i < tn; i++) vs2[Cp->nint + i] = vs[i];
            k[n++] = inst_tele(Cp->boundary, tn + Cp->nint, vs2, 0);
            Data *D = &datas[Cp->data];
            for (int j = 0; j < D->nidx; j++) if (D->idxrec[j] >= 0) k[n++] = inst_tele(Cp->ridx[j], tn, vs, 0);
        }
    }
    *ks = k; *nk = n;
    return e;
}
static Term *E_con_post(Term *t, Term **rs, int nk, void *ctx, void *aux) {
    EInfo *I = ctx; ECon *e = aux; Con *Cp = e->Cp; Term **args = e->args; int np = e->np, depth = e->depth;
    (void)nk;
    Term *m = mk_var(depth + I->n + I->htot + I->r + (I->o - 1 - Cp->bord));
    for (int j = 0; j < Cp->nargs; j++) m = mk_app(m, args[np + j], Cp->args[j].irr);   /* the elements as they are: only the hypotheses below are images (CHM: m_c a.. E(a_rec)..; M20 found the images here) */
    int r = 0;
    for (int j = 0; j < Cp->nargs; j++) if (Cp->args[j].isrec || Cp->args[j].isrecpath) {
        Term *ih = rs[r++];
        if (ih == args[np + j] || term_eq(ih, args[np + j])) die("the boundary of %s: no induction hypothesis for the argument of %s", I->C->name, Cp->name);
        m = mk_app(m, ih, 0);
    }
    if (Cp->nint == 0) return m;
    if (Cp->pathmethod) return mk_term(T_PAPP, m, args[np + Cp->nargs], rs[r], rs[r + 1]);   /* the method is a path: its endpoints the boundary's images */
    /* the method is a cube  (is : I) -> Sub (P idx (c p a is)) phi [faces -> E(boundary)]: apply it and take the element out */
    for (int q = 0; q < Cp->nint; q++) m = mk_app(m, args[np + Cp->nargs + q], 0);
    if (!Cp->boundary) return m;
    Term *sys = rs[r++];
    Term *phi = NULL;
    for (int i = 0; i < sys->nbr; i++) phi = phi ? mk_term(T_IOR, phi, sys->br[i].face, NULL, NULL) : sys->br[i].face;
    Term *A = mk_var(depth + I->n + I->htot + I->r + I->o + (I->nb - 1 - I->pi));   /* P idx [img] (c p a is) */
    Data *D = &datas[Cp->data];
    for (int j = 0; j < D->nidx; j++) {
        Term *ix = inst_tele(Cp->ridx[j], e->tn, e->vs, 0);
        A = mk_app(A, ix, 1);
        if (D->idxrec[j] >= 0) A = mk_app(A, rs[r++], 0);
    }
    A = mk_app(A, t, 0);
    return mk_term(T_OUTS, A, phi ? phi : mk_term(T_I0, NULL, NULL, NULL, NULL), sys, m);
}
static Term *E_papp_post(Term *t, Term **rs, int n, void *ctx, void *aux) { (void)n; (void)ctx; (void)aux; return mk_term(T_PAPP, rs[0], t->b, rs[1], rs[2]); }
static Term *E_sys_post(Term *t, Term **rs, int n, void *ctx, void *aux) {
    (void)n; (void)ctx; (void)aux;
    Term *r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
    for (int i = 0; i < t->nbr; i++) { r->br[i].face = t->br[i].face; r->br[i].body = rs[i]; }
    return r;
}
static int E_pre(Term *t, int depth, void *ctx, TWDecide *o) {
    EInfo *I = ctx;
    switch (t->k) {
    case T_VAR: {
        int idx = t->n - depth; o->r = t;
        if (idx >= I->n + I->htot && idx < I->n + I->htot + I->r) {
            int j = I->r - 1 - (idx - I->n - I->htot);
            if (I->record[j] >= 0) o->r = mk_var(depth + I->n + (I->htot - 1 - I->record[j]));
        }
        return TW_DONE;
    }
    case T_PAPP: o->ks = xalloc(3 * sizeof(Term *)); o->ks[0] = t->a; o->ks[1] = t->c; o->ks[2] = t->d; o->nk = 3; o->post = E_papp_post; o->fin = 1; return TW_SPINE;
    case T_APP: case T_CON: {
        ECon *e = E_con_pre(t, I, depth, &o->ks, &o->nk);
        if (e) { o->post = E_con_post; o->aux = e; o->fin = 1; return TW_SPINE; }
        if (t->k == T_CON) { o->r = t; return TW_DONE; }
        return TW_NODE;
    }
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: case T_IAND: case T_IOR: case T_INEG: o->r = t; return TW_DONE;
    case T_SYS:
        o->ks = xalloc((t->nbr + 1) * sizeof(Term *)); o->nk = t->nbr;
        for (int i = 0; i < t->nbr; i++) o->ks[i] = t->br[i].body;
        o->post = E_sys_post; o->fin = 1; return TW_SPINE;
    default: return TW_NODE;
    }
}
static Term *E_build(Term *t, Term **q, void *ctx) {
    Term *r; (void)ctx;
    switch (t->k) {
    case T_APP: return mk_app(q[0], q[1], t->irr);
    case T_PI: r = mk_pi(t->name, q[0], q[1], t->irr); r->isi = t->isi; return r;
    case T_LAM: r = mk_lam(t->name, q[0], t->irr); r->isi = t->isi; return r;
    case T_LET: return mk_let(t->name, q[0], q[1], q[2], t->irr);
    case T_SIGMA: r = mk_term(T_SIGMA, q[0], q[1], NULL, NULL); r->name = t->name; return r;
    default:
        r = mk_term(t->k, q[0], q[1], q[2], q[3]);
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; r->num = t->num; return r;
    }
}
static Term *E(Term *t, EInfo *I, int depth) { return term_walk(t, depth, 0, E_pre, E_build, I); }
/* the boundary of C at an endpoint of its single interval: the body of the branch whose face holds there (under [params, args]) */
static Term *boundary_at(Con *C, int end) {
    Term *v = mk_term(end ? T_I1 : T_I0, NULL, NULL, NULL, NULL);
    for (int i = 0; i < C->boundary->nbr; i++) {
        Val *f = eval(NULL, subst_term(C->boundary->br[i].face, 0, v));
        if (iv_is_one(f->iv)) return subst_term(C->boundary->br[i].body, 0, v);
    }
    return NULL;
}
/* rename the free variables of t: variable v (v < n) becomes map[v]; t's own d binders are passed */
typedef struct { int n; const int *map; } Remap;
static int remap_pre(Term *t, int d, void *ctx, TWDecide *o) {
    Remap *m = ctx;
    if (t->k != T_VAR) return TW_NODE;
    if (t->n < d) { o->r = t; return TW_DONE; }
    if (t->n - d >= m->n) die("internal: remap: a variable out of range");
    o->r = mk_var(m->map[t->n - d] + d); return TW_DONE;
}
static Term *remap_build(Term *t, Term **q, void *ctx) {
    Term *r; (void)ctx;
    switch (t->k) {
    case T_PI: case T_SIGMA:
        r = mk_term(t->k, q[0], q[1], NULL, NULL);
        r->name = t->name; r->irr = t->irr; r->isi = t->isi; r->pre = t->pre; r->imp = t->imp; return r;
    case T_LAM: r = mk_lam(t->name, q[0], t->irr); r->isi = t->isi; r->imp = t->imp; return r;
    case T_LET: return mk_let(t->name, q[0], q[1], q[2], t->irr);
    case T_SYS:
        r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = q[2 * i]; r->br[i].body = q[2 * i + 1]; }
        return r;
    default:
        r = mk_term(t->k, q[0], q[1], q[2], q[3]);
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; r->imp = t->imp; r->num = t->num; return r;
    }
}
/* rename the free variables of t: variable v (v < n) becomes map[v]; t's own d binders are passed */
static Term *remap(Term *t, int n, const int *map, int d) { Remap m = { n, map }; return term_walk(t, d, 0, remap_pre, remap_build, &m); }
/* the motive of a member is run-time content when hcomp is a formal element of it */
static int motive_rel(int member) { Data *M = &datas[member]; return M->hit || M->nidx > 0; }
Term *elim_type(int d, LVal lvl, int res_irr, LVal dl) {
    Data *D = data_at(d, dl); elim_dlt = mk_lval(dl);
    int np = D->nparams, m = D->nidx;
    /* the eliminators of a block share the prefix [params, P_0..P_{nbk-1}, methods of every member (K)] */
    int nbk = D->nblock, K = block_ncons(d), b0 = D->block, jpos = D->bpos;
    #define ITY(j) (D->itys[j])
    #define PTY(i) (D->ptys[i])
    #define ATY(C, j) ((C)->args[j].ty)
    /* body: P_j i_0 [img_0] .. x   under [params, P(nbk), mth(K), i(m), x]; an index ranging over member rm is followed by
       its image, its elimination by rm with the same prefix: elim D_rm p P.. m.. i_q */
    Term *body = mk_var(1 + m + K + (nbk - 1 - jpos));
    for (int q = 0; q < m; q++) {
        body = mk_app(body, mk_var(1 + (m - 1 - q)), 1);
        int rm = D->idxrec[q];
        if (rm >= 0) {
            Term *im = mk_ref_l(T_ELIM, rm, elim_dlt);
            for (int t2 = 0; t2 < np; t2++) im = mk_app(im, mk_var(1 + m + K + nbk + (np - 1 - t2)), 1);
            for (int r2 = 0; r2 < nbk; r2++) im = mk_app(im, mk_var(1 + m + K + (nbk - 1 - r2)), !motive_rel(b0 + r2));
            for (int o2 = 0; o2 < K; o2++) im = mk_app(im, mk_var(1 + m + (K - 1 - o2)), 0);
            im = mk_app(im, mk_var(1 + (m - 1 - q)), 0);
            body = mk_app(body, im, 0);
        }
    }
    body = mk_app(body, mk_var(0), 0);
    /* x : D p i */
    Term *t = mk_pi("x", data_applied(d, m + K + nbk, 0), body, 0);
    for (int j = m - 1; j >= 0; j--) t = mk_pi(xsprintf("i%d", j), shift(ITY(j), j, K + nbk), t, 1);
    /* methods: the last constructor of the last member first */
    for (int mi = nbk - 1; mi >= 0; mi--) {
      Data *M = data_at(b0 + mi, dl); int mm = M->nidx;
      for (int ci = M->ncons - 1; ci >= 0; ci--) {
        Con *C = con_at(M->cons[ci], dl); int r = C->nargs, htot = C->nrec, o = C->bord;
        int n = C->nint;
        /* recursive-argument ordinals (for the induction hypotheses' positions) */
        int *record = xalloc((r + 1) * sizeof(int)); { int oo = 0; for (int j = 0; j < r; j++) record[j] = (C->args[j].isrec || C->args[j].isrecpath) ? oo++ : -1; }
        EInfo I = { C, n, r, htot, o, nbk, mi, np, dl, record };
        /* return: P_mi ridx [img] (c p a is)   under [params, P(nbk), mth(o), a(r), ih(htot), iv(n)]; the image of an index is
           the index term with recursive arguments replaced by their hypotheses and constructors by their methods (E) */
        Term *ret = mk_var(n + htot + r + o + (nbk - 1 - mi));
        for (int j = 0; j < mm; j++) {
            Term *ix = shift2(C->ridx[j], n, htot, n + r, htot + o + nbk);
            ret = mk_app(ret, ix, 1);
            if (M->idxrec[j] >= 0) ret = mk_app(ret, E(ix, &I, 0), 0);
        }
        Term *ct = mk_ref_l(T_CON, M->cons[ci], elim_dlt);
        for (int i = 0; i < np; i++) ct = mk_app(ct, mk_var(n + htot + r + o + nbk + (np - 1 - i)), !C->bparams);
        for (int j = 0; j < r; j++) ct = mk_app(ct, mk_var(n + htot + (r - 1 - j)), C->args[j].irr);
        for (int q = 0; q < n; q++) ct = mk_app(ct, mk_var(n - 1 - q), 0);
        ret = mk_app(ret, ct, 0);
        Term *mt = ret;
        if (n > 0) {
            if (C->pathmethod) {   /* PathP (i. P (c a i)) E(b0) E(b1)   under [params, P, mth(o), a(r), ih(htot)] */
                Term *line = mk_lam("i", ret, 0); line->isi = 1;
                EInfo I0 = { C, 0, r, htot, o, nbk, mi, np, dl, record };
                Term *e0 = E(shift2(boundary_at(C, 0), 0, htot, r, htot + o + nbk), &I0, 0);
                Term *e1 = E(shift2(boundary_at(C, 1), 0, htot, r, htot + o + nbk), &I0, 0);
                mt = mk_term(T_PATHP, line, e0, e1, NULL);
            } else if (C->boundary) {   /* (is : I) -> Sub (P (c a is)) phi [faces -> E(boundary)] */
                Term *sys = E(shift2(C->boundary, n, htot, n + r, htot + o + nbk), &I, 0);
                Term *phi = NULL;
                for (int i = 0; i < sys->nbr; i++) phi = phi ? mk_term(T_IOR, phi, sys->br[i].face, NULL, NULL) : sys->br[i].face;
                mt = mk_term(T_SUB, ret, phi ? phi : mk_term(T_I0, NULL, NULL, NULL, NULL), sys, NULL);
                for (int q = n - 1; q >= 0; q--) mt = mk_pi(xsprintf("i%d", q), mk_term(T_INTERVAL, NULL, NULL, NULL, NULL), mt, 0);
            } else {
                for (int q = n - 1; q >= 0; q--) mt = mk_pi(xsprintf("i%d", q), mk_term(T_INTERVAL, NULL, NULL, NULL, NULL), mt, 0);
            }
        }
        /* induction hypotheses, last first: an argument recursive in member rm gets its hypothesis from P_rm, applied to the
           occurrence's indices and their images */
        int h = htot;
        for (int j = r - 1; j >= 0; j--) {
            ConArg *A = &C->args[j];
            int rm = (A->isrec || A->isrecpath) ? A->rec - b0 : 0;
            Data *RM = (A->isrec || A->isrecpath) ? &datas[A->rec] : NULL;
            if (A->isrecpath) {   /* PathP (k. P_rm idx [img] (a_j k)) E(px) E(py)   under [params, P, mth(o), a(r), ih(h)] */
                h--;
                EInfo Ih = { C, 0, r, h, o, nbk, mi, np, dl, record };
                Term *px = shift2(A->px, 0, h + (r - j), j, h + (r - j) + o + nbk), *py = shift2(A->py, 0, h + (r - j), j, h + (r - j) + o + nbk);
                Term *pa = mk_term(T_PAPP, mk_var((r - 1 - j) + h + 1), mk_var(0), shift(px, 0, 1), shift(py, 0, 1));
                Term *Pk = mk_var(1 + h + r + o + (nbk - 1 - rm));
                for (int q = 0; q < A->nidx; q++) {
                    Term *ix = shift(shift2(A->idx[q], 0, h + (r - j), j, h + (r - j) + o + nbk), 0, 1);
                    Pk = mk_app(Pk, ix, 1);
                    if (RM->idxrec[q] >= 0) Pk = mk_app(Pk, E(ix, &Ih, 1), 0);
                }
                Term *line = mk_lam("k", mk_app(Pk, pa, 0), 0); line->isi = 1;
                Term *ih = mk_term(T_PATHP, line, E(px, &Ih, 0), E(py, &Ih, 0), NULL);
                mt = mk_pi(xsprintf("ih%d", j), ih, mt, 0);
                continue;
            }
            if (!A->isrec) continue;
            h--;
            int q = A->npi;
            EInfo Iq = { C, 0, r, h, o, nbk, mi, np, dl, record };
            /* P_rm idx[y] [img] (a_j y..)   under [params, P, mth(o), a(r), ih(h), y(q)] */
            Term *ih = mk_var(q + h + r + o + (nbk - 1 - rm));
            for (int i = 0; i < A->nidx; i++) {
                Term *ix = shift2(A->idx[i], q, h + (r - j), q + j, h + (r - j) + o + nbk);
                ih = mk_app(ih, ix, 1);
                if (RM->idxrec[i] >= 0) ih = mk_app(ih, E(ix, &Iq, q), 0);
            }
            Term *aj = mk_var((r - 1 - j) + h + q);
            Term *aty = ATY(C, j); int yt = 1;
            for (Term *w = aty; w->k == T_PI && yt <= q; w = w->b, yt++) aj = mk_app(aj, mk_var(q - yt), w->irr);
            ih = mk_app(ih, aj, 0);
            /* wrap the y binders, innermost first */
            Term **ys = xalloc((q + 1) * sizeof(Term *)); int *yirr = xalloc((q + 1) * sizeof(int));
            { Term *w = aty; for (int tt = 0; tt < q; tt++) { ys[tt] = w->a; yirr[tt] = w->irr; w = w->b; } }
            for (int tt = q - 1; tt >= 0; tt--)
                ih = mk_pi(xsprintf("y%d", tt), shift2(ys[tt], tt, h + (r - j), tt + j, h + (r - j) + o + nbk), ih, yirr[tt]);
            mt = mk_pi(xsprintf("ih%d", j), ih, mt, res_irr);
        }
        for (int j = r - 1; j >= 0; j--) { mt = mk_pi(C->args[j].name, shift(ATY(C, j), j, o + nbk), mt, C->args[j].irr); mt->imp = C->args[j].imp; }
        t = mk_pi(xsprintf("m_%s", C->name), mt, t, 0);
      }
    }
    /* motives, the last member's first: P_i : (i_0 : I_0) [(h_0 : P_rm i_0)] .. -> D_i p i.. -> U lvl   under [params, P_0..P_{i-1}] */
    for (int mi = nbk - 1; mi >= 0; mi--) {
        Data *M = data_at(b0 + mi, dl); int mm = M->nidx; int rel = motive_rel(b0 + mi);
        int tot = mm + M->nimg;
        int *pos = xalloc((mm + 1) * sizeof(int)); { int t2 = 0; for (int q = 0; q < mm; q++) { pos[q] = t2++; if (M->idxrec[q] >= 0) t2++; } }
        Term *P = mk_ref_l(T_DATA, b0 + mi, elim_dlt);
        for (int t2 = 0; t2 < np; t2++) P = mk_app(P, mk_var(tot + mi + (np - 1 - t2)), 1);
        for (int q = 0; q < mm; q++) P = mk_app(P, mk_var(tot - 1 - pos[q]), 1);
        P = mk_pi("x", P, mk_u_l(lvl), 0);
        for (int q = mm - 1; q >= 0; q--) {
            int rm = M->idxrec[q];
            if (rm >= 0) {   /* the image of i_q: P_rm i_q   under [params, P(mi), b_0..b_{pos[q]}] */
                int tb = pos[q] + 1;
                Term *ity = mk_app(mk_var(tb + (mi - 1 - (rm - b0))), mk_var(0), 0);
                P = mk_pi(xsprintf("h%d", q), ity, P, !rel);
            }
            int tb = pos[q];   /* I_q under [params, i_0..i_{q-1}] -> under [params, P(mi), b_0..b_{tb-1}] */
            int *map = xalloc((q + np + 1) * sizeof(int));
            for (int v = 0; v < q; v++) map[v] = tb - 1 - pos[q - 1 - v];
            for (int v = 0; v < np; v++) map[q + v] = tb + mi + v;
            P = mk_pi(xsprintf("i%d", q), remap(M->itys[q], q + np, map, 0), P, !rel);
        }
        t = mk_pi(nbk == 1 ? "P" : xsprintf("P_%s", M->name), P, t, !rel);
    }
    for (int i = np - 1; i >= 0; i--) { t = mk_pi(xsprintf("p%d", i), PTY(i), t, 1); t->imp = 1; }   /* the parameters are implicit */
    return t;
    #undef ITY
    #undef PTY
    #undef ATY
}

/* ---- applications ---- */

/* the type of a global reference at a universe shift */
/* the level a global is taken at: its own hidden level inside its own declaration, else a fresh meta (solved
   at the end of the enclosing definition); not polymorphic: none */
static Term *global_level(TKind k, int id, LVal *L) {
    int d = k == T_DEF ? -1 : k == T_CON ? cons[id].data : id;
    if (k != T_DEF && IN_DECL(d)) { *L = lv_hidden(); return mk_lval(*L); }
    if (!ref_poly(k, id)) { *L = lv_const(0); return NULL; }
    int m = lv_meta_new(); *L = lv_meta(m);
    Term *t = mk_term(T_LMETA, NULL, NULL, NULL, NULL); t->n = m; return t;
}
/* an argument whose expected type is not known yet (a meta) and which cannot be inferred (a numeral, lambda, pair or system) is
   deferred: a meta stands for it in the spine, and it is checked once the type is known, at the end of the enclosing check
   in the same context (after the application's result type has met the expected type) */
typedef struct { STerm *term; Val *dom; int meta; } Deferred;
static Deferred *dnums; static int ndnums;
static int deferrable(STerm *s) { return s->k == S_NUM || s->k == S_LAM || s->k == S_PAIR || s->k == S_SYS; }
static Term *check(Ctx *c, STerm *s, Val *ty);
/* the type of an applied term is not known yet (a meta): it is a function type (x : ?D) -> ?C x with fresh metas for the
   domain and the codomain, at fresh levels; the application determines the shape, later constraints the rest */
static Val *refine_to_pi(Ctx *c, Val *ty, int line) {
    ty = force(ty);
    ty = force(ty);
    if (!(ty->k == V_NEU && ty->h == H_META)) return ty;
    /* in the meta's own context (a prefix of the current one): its solution may only use the meta's variables */
    int k = tmetas[ty->n].ctxn;
    if (k > c->n) die("line %d: internal: a meta from a deeper context", line);
    Ctx c2 = *c; c2.n = k;
    for (int i = c->n; i > k; i--) c2.env = c2.env->next;
    int l1 = lv_meta_new(), l2 = lv_meta_new();
    Term *dom = fresh_meta(&c2, vu_l(lv_meta(l1)), line);
    Val *cty = mkval(V_PI); cty->name = "x"; cty->dom = eval(c2.env, dom); cty->clo.env = c2.env; cty->clo.t = mk_u_l(lv_meta(l2));
    Term *cod = fresh_meta(&c2, cty, line);
    Term *pi = mk_pi("x", dom, mk_app(shift(cod, 0, 1), mk_var(0), 0), 0);
    if (!conv(k, ty, eval(c2.env, pi))) die("line %d: the type of an applied term is not known here and cannot be a function type", line);
    return force(ty);
}

static int is_word_type(Ctx *c, Val *ty);
static void check_wordop_type(int code, Val *vty, int line, const char *name);
static void need_args(STerm *h, int n, int want, const char *what) {
    if (n < want) die("line %d: %s needs %d argument%s", h->line, what, want, want == 1 ? "" : "s");
}
/* the faces of phi as a list; dies if phi is not an interval value */
static int faces_of(Val *phi, Face **fs) { if (phi->k != V_I) die("internal: face expected"); return iv_faces(phi->iv, fs); }


/* ---- systems ---- */

typedef Val *(*TypeAt)(const Face *f, void *data);
static Val *partial_type_at(const Face *f, void *data) { return restrict_val((Val *)data, f); }
static Val *glue_type_at(const Face *f, void *data) {   /* the glued type T on a face: fst of the (T, e) there */
    Val *Te = vsys_at((Val *)data, f);
    if (!Te) die("internal: glue: no glued type on this face");
    return vproj(Te, 1);
}

/* ---- terms ---- */


/* a data type shaped like the naturals: no parameters or indices, exactly two constructors, one nullary and one
   with a single recursive argument. Returns 1 and the two constructors' ids. */
int peano_shape(int d, int *zero, int *suc) {
    Data *D = &datas[d];
    if (D->nparams || D->nidx || D->ncons != 2) return 0;
    *zero = *suc = -1;
    for (int ci = 0; ci < 2; ci++) {
        Con *C = &cons[D->cons[ci]];
        if (C->nint) return 0;
        if (C->nargs == 0) *zero = D->cons[ci];
        else if (C->nargs == 1 && C->args[0].isrec && C->args[0].npi == 0 && !C->args[0].isrecpath) *suc = D->cons[ci];
    }
    return *zero >= 0 && *suc >= 0;
}
/* the numeral n at a type shaped like the naturals, as a term of size O(log n):
     let s1 := suc in let s2 := \x -> s1 (s1 x) in ... in s_{2^k} (... (s_{2^j} zero))
   one let per bit of n, applied along the bits that are set */
/* the registered word type? (a closed irrelevant Sigma: pointer identity first, conversion otherwise) */
static int is_word_type(Ctx *c, Val *ty) {
    if (word_type < 0 || ty->k != V_SIGMA || !ty->irr) return 0;
    return ty == defs[word_type].vval || conv(c->n, ty, defs[word_type].vval);
}

static Term *check_numeral(Ctx *c, STerm *s, Val *ty) {
    int zi, si;   /* a numeral at the word type is check1's: the pair (n, refl) */
    if (ty->k == V_LEVEL) {   /* a numeral is also a constant level */
        if (s->num > 1000000) die("line %d: the level %s is too large", s->line, s->digits);
        return mk_lval(lv_add(BASE_LEVEL(c), (int)s->num));
    }
    if (ty->k != V_DATA || ty->args.n != 0 || !peano_shape(ty->n, &zi, &si))
        die("line %d: the numeral %s needs a type shaped like the naturals (a nullary constructor and one with a single recursive argument), not %s", s->line, s->digits, show(c, ty));
    Bn *n = bn_from_dec(s->digits);
    if (!n) die("line %d: malformed numeral %s", s->line, s->digits);
    return mk_num(ty->n, mk_lval(ty->lvl), n);   /* a literal value in the checker (M15); erasure spells it out (numeral_term) */
}

Term *numeral_term(int d, Term *lt, const Bn *n) {
    int zi, si;
    if (!peano_shape(d, &zi, &si)) die("internal: a literal of a type not shaped like the naturals");
    Term *zero = mk_ref_l(T_CON, zi, lt), *suc = mk_ref_l(T_CON, si, lt), *D = mk_ref_l(T_DATA, d, lt);
    if (bn_is_zero(n)) return zero;
    int K = bn_bitlen(n);
    if (K == 1) return mk_app(suc, zero, 0);
    Term *body = zero;
    for (int i = 0; i < K; i++) if (bn_bit(n, i)) body = mk_app(mk_var(K - 1 - i), body, 0);
    for (int i = K - 1; i >= 0; i--) {   /* s_i doubles s_{i-1}: s_i = \x -> s_{i-1} (s_{i-1} x), s_0 = suc */
        char *name = xalloc(32); snprintf(name, 32, "s%d", i);
        Term *val = i == 0 ? suc : mk_lam("x", mk_app(mk_var(1), mk_app(mk_var(1), mk_var(0), 0), 0), 0);
        body = mk_let(name, mk_pi("_", D, D, 0), val, body, 0);
    }
    return body;
}

/* the type of a word operation: Word -> Word -> R, with R = Word (arithmetic), a data type of two nullary constructors (weq wlt:
   the first is true, K at run time), or Sigma Word (\_ -> Word) (waddc wsubb wmull wdivmod) */
static void check_wordop_type(int code, Val *vty, int line, const char *name) {
    Val *W = defs[word_type].vval;
    Val *t = force(vty);
    if (t->k != V_PI || t->imp || t->irr || t->isi || !conv(0, force(t->dom), W)) goto bad;
    Val *cod = force(inst(&t->clo, vvar(0)));
    if (cod->k != V_PI || cod->imp || cod->irr || cod->isi || !conv(1, force(cod->dom), W)) goto bad;
    Val *res = force(inst(&cod->clo, vvar(1)));
    if (code <= 8) { if (!conv(2, res, W)) goto bad; }
    else if (code <= 10) {
        if (res->k != V_DATA || res->args.n != 0 || datas[res->n].ncons != 2) goto bad;
        for (int i = 0; i < 2; i++) { Con *C = &cons[datas[res->n].cons[i]]; if (C->nargs || C->nint) goto bad; }
    } else {
        if (res->k != V_SIGMA || res->irr || !conv(2, force(res->dom), W)) goto bad;
        if (!conv(3, force(inst(&res->clo, vvar(2))), W)) goto bad;
    }
    return;
bad:
    die("line %d: word %s: the type must be Word -> Word -> %s", line, name,
        code <= 8 ? "Word" : code <= 10 ? "B for a data type B of two nullary constructors" : "Sigma Word (\\_ -> Word)");
}

/* the type of a native definition: D -> D -> D for a data type D shaped like the naturals; returns D */
static int native_type_data(Val *vty, int line, const char *name) {
    Val *t = force(vty);
    int zi, si;
    if (t->k != V_PI || t->imp || t->irr || t->isi) goto bad;
    Val *dom = force(t->dom);
    if (dom->k != V_DATA || dom->args.n != 0 || !peano_shape(dom->n, &zi, &si)) goto bad;
    Val *cod = force(inst(&t->clo, vvar(0)));
    if (cod->k != V_PI || cod->imp || cod->irr || cod->isi || !conv(1, cod->dom, dom)) goto bad;
    Val *res = force(inst(&cod->clo, vvar(1)));
    if (!conv(2, res, dom)) goto bad;
    return dom->n;
bad:
    die("line %d: native %s: the type must be D -> D -> D for a data type D shaped like the naturals", line, name);
    return -1;
}
/* ---- the elaborator on the machine (S4b) ----
   check, infer and their helpers are frames on the evaluator's machine (machine.h), so elaboration's depth is bounded by
   memory alone, as evaluation's is. A frame's term result travels through the register; infer's type, a sort's level and
   pretype flag through the elaborator's registers below, read by the caller right after the call returns. A frame keeps
   everything that outlives a call in its fields (the stack may move); a context restricted to a face lives on the heap.
   The evaluator's entry points (eval, conv, force, quote, ...) are called as C: evaluation never enters the elaborator, so
   each nests one driver run. */
static Val *eret_ty;   /* infer's type */
static LVal eret_lvl;  /* a sort's level */
static int eret_pre;   /* a sort is a pretype */
typedef struct {
    MHdr h;
    Ctx *c; STerm *s; Val *ty;
    STerm **args, *hs, *ms; int n, ai, i, j, nb, depth, nf, d, np, m0, d0, pa, pb, irr, all, isl;
    Term *t, *a, *b, *u, *line, *phi, *head, *tst, *rt, **pt, *dlt;
    Val *v, *x, *got, *hty, *lv, *pv, *Av, *uv, *u0v, *tsv, **psi, **pvv, **iv;
    Env *pe, *ie; Data *D, *DV, *DV0;
    LVal la, lb, dl;
    Face *fs; Ctx *rc;
    TypeAt tyat; void *data;
    const char *nm;
} ElabF;
#define F ((ElabF *)(mst.p + off))
static void check_step(size_t off);
static void check1_step(size_t off);
static void infer_step(size_t off);
static void infer_app_step(size_t off);
static void infer_elim_step(size_t off);
static void app_spine_step(size_t off);
static void sort_step(size_t off);
static void check_line_step(size_t off);
static void system_step(size_t off);
static void resolve_step(size_t off);
static ElabF *epush(void (*step)(size_t), Ctx *c, STerm *s, Val *ty) { ElabF *f = mpush(sizeof *f, step); f->c = c; f->s = s; f->ty = ty; return f; }
static void mpush_check(Ctx *c, STerm *s, Val *ty) { epush(check_step, c, s, ty); }
static void mpush_infer(Ctx *c, STerm *s) { epush(infer_step, c, s, NULL); }
/* a type of either sort (pre: 1 also refuses pretypes: a type in a universe, with Kan structure) */
static void mpush_sort(Ctx *c, STerm *s, int kan) { epush(sort_step, c, s, NULL)->isl = kan; }
static void mpush_check_line(Ctx *c, STerm *s) { epush(check_line_step, c, s, NULL); }
static void mpush_system_at(Ctx *c, STerm *s, Val *phi, TypeAt tyat, void *data) { ElabF *f = epush(system_step, c, s, phi); f->tyat = tyat; f->data = data; }
static void mpush_resolve(Ctx *c, int all) { epush(resolve_step, c, NULL, NULL)->all = all; }
static void mpush_app_spine(Ctx *c, STerm **args, int nargs, Term *head, Val *hty) {
    ElabF *f = epush(app_spine_step, c, NULL, NULL); f->args = args; f->n = nargs; f->head = head; f->hty = hty;
}

/* a term must be a type (of either sort, or with isl a type in a universe): its core, universe level and whether it is a
   pretype; a type whose sort is not known yet (a meta) is in a universe at a fresh level */
static void sort_step(size_t off) {
    MSTART
    F->c->irrpos++;   /* a type is an irrelevant position */
    MCALL(mpush_infer(F->c, F->s)); F->t = MTERM(); F->v = eret_ty;
    F->c->irrpos--;
    { Val *ty = refine_to_universe(F->c, F->v);
      if (ty->k != V_U) die("line %d: expected a type, but %s : %s", F->s->line, "the term", show(F->c, ty));
      if (F->isl && ty->pre) die("line %d: a type in a universe is needed here, but the term is a pretype (Partial, Sub, Level, or a function from I) and has no Kan structure", F->s->line);
      eret_lvl = ty->lvl; eret_pre = ty->pre; }
    MRETT(F->t);
    MFINISH
}
/* a line of types  (i : I) -> U l : either a lambda over an interval variable, or a term whose type is such a function */
static void check_line_step(size_t off) {
    MSTART
    if (F->s->k == S_LAM) {
        ctx_bind_i(F->c, F->s->binders[0].name);
        MCALL(mpush_sort(F->c, F->s->a, 1)); F->t = MTERM(); F->la = eret_lvl;
        ctx_pop(F->c);
        { Term *t = mk_lam(F->s->binders[0].name, F->t, 0); t->isi = 1; eret_lvl = F->la; MRETT(t); }
    }
    MCALL(mpush_infer(F->c, F->s)); F->t = MTERM(); F->v = eret_ty;
    { Val *ty = force(F->v); STerm *s = F->s; Ctx *c = F->c;
      if (ty->k != V_PI || !ty->isi) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
      Val *cod = refine_to_universe(c, inst(&ty->clo, vivar(c->n)));
      if (cod->k != V_U) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
      if (cod->pre) die("line %d: expected a line of types (i : I) -> U, but the line yields pretypes: %s", s->line, show(c, ty));
      eret_lvl = cod->lvl; }
    MRETT(F->t);
    MFINISH
}
/* the deferred arguments whose types are known now, checked in this context (a check may defer further arguments) */
static void resolve_step(size_t off) {
    MSTART
    for (;;) {
        { int found = -1;
          for (int i = 0; i < ndnums && found < 0; i++) {
              Val *dom = force(dnums[i].dom);
              if (!(dom->k == V_NEU && dom->h == H_META) && tmetas[dnums[i].meta].ctxn == F->c->n) found = i;
          }
          if (found < 0) break;
          Deferred d = dnums[found]; dnums[found] = dnums[--ndnums];
          F->i = d.meta; F->s = d.term; F->v = d.dom; }
        MCALL(mpush_check(F->c, F->s, force(F->v)));
        meta_assign(F->i, MTERM(), tmetas[F->i].ctxn);
    }
    if (F->all && ndnums > 0) die("line %d: the type of this argument is not determined by its use; write the implicit argument, f {e} ..", dnums[0].term->line);
    MRET(NULL);
    MFINISH
}
/* a head applied along a spine of arguments */
static void app_spine_step(size_t off) {
    MSTART
    F->hty = force(F->hty);
    for (F->i = 0; F->i < F->n; F->i++) {
        { Ctx *c = F->c; STerm *ai = F->args[F->i]; Val *hty = force(F->hty); Term *head = F->head;
          while (hty->k == V_PI && hty->imp && !ai->imp) {   /* an implicit argument not written: a meta */
              Term *m = fresh_meta(c, hty->dom, ai->line);
              head = mk_app(head, m, hty->irr); hty = force(inst(&hty->clo, eval(c->env, m)));
          }
          hty = refine_to_pi(c, hty, ai->line);
          F->hty = hty; F->head = head;
          if (hty->k == V_PI && deferrable(ai)) {   /* against a type not known yet: checked once the spine has met its expected type */
              Val *dom = force(hty->dom);
              if (dom->k == V_NEU && dom->h == H_META) {
                  int id = meta_new(dom, c->n, c->names, c->tys, ai->line); Term *m = meta_term(id, c->n); tmetas[id].deferred = 1;
                  dnums = rrealloc(dnums, (ndnums + 1) * sizeof(Deferred));
                  dnums[ndnums].term = ai; dnums[ndnums].dom = dom; dnums[ndnums].meta = id; ndnums++;
                  F->head = mk_app(head, m, hty->irr); F->hty = inst(&hty->clo, eval(c->env, m));
                  continue;
              }
          }
          if (hty->k != V_PATHP && hty->k != V_PI) die("line %d: applying a non-function of type %s", ai->line, show(c, hty)); }
        if (F->hty->k == V_PATHP) {
            MCALL(mpush_check(F->c, F->args[F->i], vinterval()));
            { Term *r = MTERM(); Ctx *c = F->c; Val *hty = F->hty;
              F->head = mk_term(T_PAPP, F->head, r, quote(c->n, hty->b), quote(c->n, hty->c));
              F->hty = vapp(hty->a, eval(c->env, r), 0); }
            continue;
        }
        if (F->hty->irr & 2) { F->c->irrpos++; F->c->irrlen++; }   /* the argument of an irrelevant binder */
        MCALL(mpush_check(F->c, F->args[F->i], F->hty->dom));
        if (F->hty->irr & 2) { F->c->irrpos--; F->c->irrlen--; }
        { Term *a = MTERM();
          F->head = mk_app(F->head, a, F->hty->irr);
          F->hty = inst(&F->hty->clo, eval(F->c->env, a)); }
    }
    eret_ty = F->hty; MRETT(F->head);
    MFINISH
}

/* ---- applications and the formers written as heads ---- */
static void infer_app_step(size_t off) {
    MSTART
    {   STerm **args = NULL; int n = 0, cap = 0; STerm *h = F->s;
        while (h->k == S_APP) {
            if (n == cap) { cap = cap ? 2 * cap : 8; STerm **na = xalloc(cap * sizeof(STerm *)); if (n) memcpy(na, args, n * sizeof(STerm *)); args = na; }
            args[n++] = h->b; h = h->a;
        }
        for (int i = 0; i < n / 2; i++) { STerm *t = args[i]; args[i] = args[n - 1 - i]; args[n - 1 - i] = t; }
        F->args = args; F->n = n; F->hs = h; }
    #define C_ F->c
    #define A_(i) F->args[i]
    if (F->hs->k == S_ELIM) MBECOME(infer_elim_step);
    if (F->hs->k == S_PATHP) {
        if (F->hs->lvl == 0) {   /* PathP line x y */
            need_args(F->hs, F->n, 3, "PathP");
            MCALL(mpush_check_line(C_, A_(0))); F->line = MTERM(); F->la = eret_lvl;
        } else {                 /* Path A x y = PathP (\_ -> A) x y */
            need_args(F->hs, F->n, 3, "Path");
            MCALL(mpush_sort(C_, A_(0), 1)); F->la = eret_lvl;
            F->line = mk_lam("_", shift(MTERM(), 0, 1), 0); F->line->isi = 1;
        }
        F->lv = eval(C_->env, F->line);
        MCALL(mpush_check(C_, A_(1), vapp(F->lv, vi(iv_zero()), 0))); F->a = MTERM();
        MCALL(mpush_check(C_, A_(2), vapp(F->lv, vi(iv_one()), 0))); F->b = MTERM();
        { STerm **a = F->args + 3; int n = F->n - 3; Ctx *c = C_; Term *t = mk_term(T_PATHP, F->line, F->a, F->b, NULL); Val *u = vu_l(F->la);
          MTAIL(mpush_app_spine(c, a, n, t, u)); }
    }
    if (F->hs->k == S_PARTIAL) {
        need_args(F->hs, F->n, 2, "Partial");
        MCALL(mpush_check(C_, A_(0), vinterval())); F->phi = MTERM();
        MCALL(mpush_sort(C_, A_(1), 1)); F->la = eret_lvl;
        { STerm **a = F->args + 2; int n = F->n - 2; Ctx *c = C_; Term *t = mk_term(T_PARTIAL, F->phi, MTERM(), NULL, NULL); Val *u = vupre_l(F->la);
          MTAIL(mpush_app_spine(c, a, n, t, u)); }
    }
    if (F->hs->k == S_TRANSP) {
        need_args(F->hs, F->n, 3, "transp");
        MCALL(mpush_check_line(C_, A_(0))); F->line = MTERM(); F->la = eret_lvl;
        F->lv = eval(C_->env, F->line);
        MCALL(mpush_check(C_, A_(1), vinterval())); F->phi = MTERM(); F->pv = eval(C_->env, F->phi);
        MCALL(mpush_check(C_, A_(2), vapp(F->lv, vi(iv_zero()), 0))); F->u = MTERM();
        {   /* the line must be constant wherever phi holds */
            Ctx *c = C_; Val *lv = F->lv;
            Val *Ai = vapp(lv, vivar(c->n), 0), *A0 = vapp(lv, vi(iv_zero()), 0);
            Face *fs; int nf = faces_of(F->pv, &fs);
            for (int i = 0; i < nf; i++)
                if (!conv(c->n + 1, restrict_val(Ai, &fs[i]), restrict_val(A0, &fs[i])))
                    die("line %d: transp: the line %s is not constant on the face where it must be the identity", A_(0)->line, show(c, lv));
            Term *t = mk_term(T_TRANSP, F->line, F->phi, F->u, NULL);
            t->n = !val_mentions_ivar(c->n + 1, Ai, c->n);     /* a constant line: erasure may drop the transport */
            STerm **a = F->args + 3; int n = F->n - 3; Val *r = vapp(lv, vi(iv_one()), 0);
            MTAIL(mpush_app_spine(c, a, n, t, r)); }
    }
    if (F->hs->k == S_HCOMP) {
        need_args(F->hs, F->n, 4, "hcomp");
        MCALL(mpush_sort(C_, A_(0), 1)); F->t = MTERM(); F->Av = force(eval(C_->env, F->t));
        MCALL(mpush_check(C_, A_(1), vinterval())); F->phi = MTERM(); F->pv = eval(C_->env, F->phi);
        {   /* u : (i : I) -> Partial phi A */
            Val *uty = mkval(V_PI); uty->name = "i"; uty->isi = 1; uty->dom = vinterval();
            uty->clo.env = C_->env; uty->clo.t = mk_term(T_PARTIAL, shift(F->phi, 0, 1), shift(F->t, 0, 1), NULL, NULL);
            F->v = uty; }
        MCALL(mpush_check(C_, A_(2), F->v)); F->u = MTERM(); F->uv = eval(C_->env, F->u);
        MCALL(mpush_check(C_, A_(3), F->Av)); F->a = MTERM(); F->u0v = eval(C_->env, F->a);
        {   /* the base must agree with the sides at i0 wherever phi holds */
            Ctx *c = C_; Face *fs; int nf = faces_of(F->pv, &fs);
            for (int i = 0; i < nf; i++) {
                Val *side = vsys_at(vapp(F->uv, vi(iv_zero()), 0), &fs[i]);
                if (!side) die("line %d: hcomp: the sides do not cover their face", A_(2)->line);
                if (!conv(c->n, side, restrict_val(F->u0v, &fs[i])))
                    die("line %d: hcomp: the base does not agree with the sides at i0 on a face of %s\n  side = %s\n  base = %s", A_(3)->line, show(c, F->pv), show(c, side), show(c, restrict_val(F->u0v, &fs[i])));
            }
            Term *t = mk_term(T_HCOMP, F->t, F->phi, F->u, F->a); t->n = (F->Av->k == V_U);
            STerm **a = F->args + 4; int n = F->n - 4; Val *Av = F->Av;
            MTAIL(mpush_app_spine(c, a, n, t, Av)); }
    }
    if (F->hs->k == S_COMP) {
        /* comp A phi u u0 : A i1  with  u : (i : I) -> Partial phi (A i),  u0 : A i0 agreeing with u i0 on phi.
           Elaborated to its definition in terms of hcomp and transp (Cohen-Huber-Mortberg):
             hcomp (A i1) phi (\i -> [ phi -> transp (\j -> A (i \/ j)) i (u i) ]) (transp A i0 u0)   */
        need_args(F->hs, F->n, 4, "comp");
        MCALL(mpush_check_line(C_, A_(0))); F->line = MTERM(); F->lv = eval(C_->env, F->line);
        MCALL(mpush_check(C_, A_(1), vinterval())); F->phi = MTERM(); F->pv = eval(C_->env, F->phi);
        {   Val *uty = mkval(V_PI); uty->name = "i"; uty->isi = 1; uty->dom = vinterval();
            uty->clo.env = C_->env; uty->clo.t = mk_term(T_PARTIAL, shift(F->phi, 0, 1), mk_app(shift(F->line, 0, 1), mk_var(0), 0), NULL, NULL);
            F->v = uty; }
        MCALL(mpush_check(C_, A_(2), F->v)); F->u = MTERM(); F->uv = eval(C_->env, F->u);
        MCALL(mpush_check(C_, A_(3), vapp(F->lv, vi(iv_zero()), 0))); F->a = MTERM(); F->u0v = eval(C_->env, F->a);
        {   Ctx *c = C_; Term *line = F->line, *phi = F->phi, *u = F->u, *u0 = F->a; Val *lv = F->lv;
            Face *fs; int nf = faces_of(F->pv, &fs);
            for (int i = 0; i < nf; i++) {
                Val *side = vsys_at(vapp(F->uv, vi(iv_zero()), 0), &fs[i]);
                if (!side) die("line %d: comp: the sides do not cover their face", A_(2)->line);
                if (!conv(c->n, side, restrict_val(F->u0v, &fs[i])))
                    die("line %d: comp: the base does not agree with the sides at i0 on a face of %s", A_(3)->line, show(c, F->pv));
            }
            int constline = !val_mentions_ivar(c->n + 1, vapp(lv, vivar(c->n), 0), c->n);
            Term *A1 = mk_app(line, mk_term(T_I1, NULL, NULL, NULL, NULL), 0);
            /* under \i: */
            Term *iv_ = mk_var(0);
            Term *inner_line = mk_lam("j", mk_app(shift(line, 0, 2), mk_term(T_IOR, mk_var(1), mk_var(0), NULL, NULL), 0), 0); inner_line->isi = 1;
            Term *tr = mk_term(T_TRANSP, inner_line, iv_, mk_app(shift(u, 0, 1), iv_, 0), NULL); tr->n = constline;
            Term *sys = mk_term(T_SYS, NULL, NULL, NULL, NULL); sys->nbr = 1; sys->br = xalloc(sizeof(TBranch));
            sys->br[0].face = shift(phi, 0, 1); sys->br[0].body = tr;
            Term *sides = mk_lam("i", sys, 0); sides->isi = 1;
            Term *base = mk_term(T_TRANSP, line, mk_term(T_I0, NULL, NULL, NULL, NULL), u0, NULL); base->n = constline;
            Term *t = mk_term(T_HCOMP, A1, phi, sides, base); t->n = (vapp(lv, vi(iv_one()), 0)->k == V_U);
            STerm **a = F->args + 4; int n = F->n - 4; Val *r = vapp(lv, vi(iv_one()), 0);
            MTAIL(mpush_app_spine(c, a, n, t, r)); }
    }
    if (F->hs->k == S_SUB) {   /* Sub A phi u : U,  u : Partial phi A */
        need_args(F->hs, F->n, 3, "Sub");
        MCALL(mpush_sort(C_, A_(0), 1)); F->t = MTERM(); F->la = eret_lvl; F->Av = force(eval(C_->env, F->t));
        MCALL(mpush_check(C_, A_(1), vinterval())); F->phi = MTERM(); F->pv = eval(C_->env, F->phi);
        { Val *pty = mkval(V_PARTIAL); pty->a = F->pv; pty->b = F->Av; F->v = pty; }
        MCALL(mpush_check(C_, A_(2), F->v));
        { STerm **a = F->args + 3; int n = F->n - 3; Ctx *c = C_; Term *t = mk_term(T_SUB, F->t, F->phi, MTERM(), NULL); Val *u = vupre_l(F->la);
          MTAIL(mpush_app_spine(c, a, n, t, u)); }
    }
    if (F->hs->k == S_SIGMA) {  /* Sigma A B : U,  B : A -> U (a lambda, or a term of that type) */
        need_args(F->hs, F->n, 2, "Sigma");
        MCALL(mpush_sort(C_, A_(0), 1)); F->t = MTERM(); F->la = eret_lvl; F->Av = force(eval(C_->env, F->t));
        if (A_(1)->k == S_LAM) {
            ctx_bind(C_, A_(1)->binders[0].name, F->Av);
            MCALL(mpush_sort(C_, A_(1)->a, 1)); F->b = MTERM(); F->lb = eret_lvl;
            ctx_pop(C_);
            { Term *t = mk_term(T_SIGMA, F->t, F->b, NULL, NULL); t->name = A_(1)->binders[0].name; t->irr = A_(1)->irrel;
              STerm **a = F->args + 2; int n = F->n - 2; Ctx *c = C_; Val *u = vu_l(lv_max(F->la, F->lb));
              MTAIL(mpush_app_spine(c, a, n, t, u)); }
        }
        MCALL(mpush_infer(C_, A_(1))); F->b = MTERM(); F->v = eret_ty;
        { Val *bty = F->v; Ctx *c = C_;
          if (bty->k != V_PI) die("line %d: the second argument of Sigma must be a family A -> U", A_(1)->line);
          expect_conv(c, A_(1)->line, bty->dom, F->Av, "family domain");
          Val *cod = inst(&bty->clo, vvar(c->n));
          if (cod->k != V_U || cod->pre) die("line %d: the second argument of Sigma must be a family A -> U", A_(1)->line);
          LVal lb = cod->lvl;
          Term *t = mk_term(T_SIGMA, F->t, mk_app(shift(F->b, 0, 1), mk_var(0), 0), NULL, NULL); t->name = "x"; t->irr = A_(1)->irrel;
          STerm **a = F->args + 2; int n = F->n - 2; Val *u = vu_l(lv_max(F->la, lb));
          MTAIL(mpush_app_spine(c, a, n, t, u)); }
    }
    if (F->hs->k == S_FST || F->hs->k == S_SND) {
        need_args(F->hs, F->n, 1, F->hs->k == S_FST ? "fst" : "snd");
        MCALL(mpush_infer(C_, A_(0))); F->t = MTERM(); F->v = eret_ty;
        { Ctx *c = C_; STerm *h = F->hs; Val *pty = force(F->v); Term *p = F->t;
          if (pty->k != V_SIGMA) die("line %d: projection from a term of type %s, expected a Sigma type", A_(0)->line, show(c, pty));
          if (h->k == S_SND && pty->irr && !c->irrpos)
              die("line %d: the second component of this pair is irrelevant; it may be projected only in an irrelevant position (the argument of an irrelevant binder, an irrelevant component)", A_(0)->line);
          Term *t = mk_term(h->k == S_FST ? T_FST : T_SND, p, NULL, NULL, NULL);
          if (is_word_type(c, pty)) t->n = 1;
          t->irr = pty->irr;   /* from an irrelevant pair: at run time the pair is its first component (M19) */
          Val *rty = h->k == S_FST ? pty->dom : inst(&pty->clo, vproj(eval(c->env, p), 1));
          STerm **a = F->args + 1; int n = F->n - 1;
          MTAIL(mpush_app_spine(c, a, n, t, rty)); }
    }
    if (F->hs->k == S_GLUE) {   /* Glue A phi Te : U,  Te : Partial phi (Sigma U (\T -> Equiv T A)) */
        need_args(F->hs, F->n, 3, "Glue");
        MCALL(mpush_sort(C_, A_(0), 1)); F->t = MTERM(); F->la = eret_lvl; F->Av = force(eval(C_->env, F->t));
        MCALL(mpush_check(C_, A_(1), vinterval())); F->phi = MTERM(); F->pv = eval(C_->env, F->phi);
        {   int eq = find_def("Equiv"); if (eq < 0) die("line %d: Glue needs the definition 'Equiv' (in the prelude)", F->hs->line);
            Val *sig = mkval(V_SIGMA); sig->name = "T"; sig->dom = vu_l(F->la);
            sig->clo.env = env_push(C_->env, F->Av);   /* under [.., A]: Equiv^lvl T A with T the bound variable */
            sig->clo.t = mk_app(mk_app(mk_ref_l(T_DEF, eq, mk_lval(F->la)), mk_var(0), 0), mk_var(1), 0);
            Val *pty = mkval(V_PARTIAL); pty->a = F->pv; pty->b = sig; F->v = pty; }
        MCALL(mpush_check(C_, A_(2), F->v));
        { Term *g = mk_term(T_GLUE, F->t, F->phi, MTERM(), mk_lval(F->la));   /* the level, for the rules' equivProof */
          STerm **a = F->args + 3; int n = F->n - 3; Ctx *c = C_; Val *u = vu_l(F->la);
          MTAIL(mpush_app_spine(c, a, n, g, u)); }
    }
    if (F->hs->k == S_GLUEEL) die("line %d: glue must be checked against a Glue type", F->hs->line);
    if (F->hs->k == S_UNGLUE) {
        need_args(F->hs, F->n, 1, "unglue");
        MCALL(mpush_infer(C_, A_(0))); F->t = MTERM(); F->v = eret_ty;
        { Ctx *c = C_; Val *bty = force(F->v);
          if (bty->k != V_GLUE) die("line %d: unglue applied to a term of type %s, expected a Glue type", A_(0)->line, show(c, bty));
          Term *t = mk_term(T_UNGLUE, F->t, quote(c->n, bty->a), quote(c->n, bty->b), quote(c->n, bty->c));
          STerm **a = F->args + 1; int n = F->n - 1; Val *r = bty->a;
          MTAIL(mpush_app_spine(c, a, n, t, r)); }
    }
    if (F->hs->k == S_INS) die("line %d: inS must be checked against a Sub type", F->hs->line);
    if (F->hs->k == S_OUTS) {  /* outS s : A  for s : Sub A phi u */
        need_args(F->hs, F->n, 1, "outS");
        MCALL(mpush_infer(C_, A_(0))); F->t = MTERM(); F->v = eret_ty;
        { Ctx *c = C_; Val *sty = force(F->v);
          if (sty->k != V_SUB) die("line %d: outS applied to a term of type %s, expected a Sub type", A_(0)->line, show(c, sty));
          Term *t = mk_term(T_OUTS, quote(c->n, sty->a), quote(c->n, sty->b), quote(c->n, sty->c), F->t);
          STerm **a = F->args + 1; int n = F->n - 1; Val *r = sty->a;
          MTAIL(mpush_app_spine(c, a, n, t, r)); }
    }
    MCALL(mpush_infer(C_, F->hs)); F->t = MTERM(); F->v = eret_ty;
    { STerm **a = F->args; int n = F->n; Ctx *c = C_; Term *head = F->t; Val *hty = F->v;
      MTAIL(mpush_app_spine(c, a, n, head, hty)); }
    MFINISH
}
/* elim D {p..} P m.. i.. x */
static void infer_elim_step(size_t off) {
    MSTART
    {   STerm *h = F->hs;
        F->d = find_data(h->name);
        if (F->d >= 0 && IN_DECL(F->d))   /* its constructors are not all declared yet: an eliminator here would have too few methods */
            die("line %d: elim %s inside the declaration of %s: the type is not complete yet", F->s->line, h->name, h->name);
        if (F->d < 0) die("line %d: elim of unknown data type '%s'", h->line, h->name);
        F->D = &datas[F->d]; F->np = F->D->nparams;
        /* the data type is taken at a fresh level (a meta, solved at the end of the definition), or at its
           own hidden level inside its own declaration */
        F->dlt = global_level(T_DATA, F->d, &F->dl);
        F->DV = data_at(F->d, F->dl);
        F->pe = NULL; F->pvv = xalloc((F->np + 1) * sizeof(Val *)); F->pt = xalloc((F->np + 1) * sizeof(Term *)); F->ai = 0; }
    for (F->i = 0; F->i < F->np; F->i++) {   /* the parameters are implicit: written {p}, or metas */
        F->v = eval(F->pe, F->DV->ptys[F->i]);
        if (F->ai < F->n && F->args[F->ai]->imp) { F->ai++; MCALL(mpush_check(F->c, F->args[F->ai - 1], F->v)); F->pt[F->i] = MTERM(); }
        else F->pt[F->i] = fresh_meta(F->c, F->v, F->hs->line);
        F->pvv[F->i] = eval(F->c->env, F->pt[F->i]); F->pe = env_push(F->pe, F->pvv[F->i]);
    }
    if (F->n < F->ai + 1) die("line %d: elim %s needs a motive", F->hs->line, F->D->name);
    /* motive: peel its lambdas against the expected binders (indices, then the target),
       then read the universe of what remains */
    #define TARGET_TYPE(dst) do { \
        Val *dv_ = mkval(V_DATA); dv_->n = F->d0; dv_->lvl = F->dl; \
        for (int i_ = 0; i_ < F->np; i_++) { vl_push(&dv_->args, F->pvv[i_], 1); } \
        for (int j_ = 0; j_ < F->m0; j_++) { vl_push(&dv_->args, F->iv[j_], 1); } \
        (dst) = dv_; } while (0)
    {   F->ms = F->args[F->ai]; F->ie = F->pe; F->nb = 0; F->depth = F->c->n;
        F->d0 = F->D->block; F->m0 = datas[F->d0].nidx; F->DV0 = data_at(F->d0, F->dl);   /* the first motive is the block's first member's */
        F->iv = xalloc((F->m0 + 2) * sizeof(Val *));
        while (F->nb <= F->m0 && F->ms->k == S_LAM) {
            Val *dom;
            if (F->nb < F->m0) dom = eval(F->ie, F->DV0->itys[F->nb]); else TARGET_TYPE(dom);
            ctx_bind(F->c, F->ms->binders[0].name, dom);
            Val *x = vvar(F->c->n - 1); F->depth = F->c->n;
            if (F->nb < F->m0) { F->iv[F->nb] = x; F->ie = env_push(F->ie, x); }
            F->ms = F->ms->a; F->nb++;
        } }
    MCALL(mpush_infer(F->c, F->ms)); F->rt = MTERM(); F->v = eret_ty;
    {   Ctx *c = F->c; STerm *ms = F->ms; Val *cur = F->v; int depth = F->depth, nb = F->nb, m0 = F->m0;
        for (int j = nb; j <= m0; j++) {
            if (cur->k != V_PI) die("line %d: motive for %s must abstract over %d index%s and the target", ms->line, datas[F->d0].name, m0, m0 == 1 ? "" : "es");
            Val *dom;
            if (j < m0) dom = eval(F->ie, F->DV0->itys[j]); else TARGET_TYPE(dom);
            expect_conv(c, ms->line, cur->dom, dom, "motive binder");
            Val *x = vvar(depth++);
            if (j < m0) { F->iv[j] = x; F->ie = env_push(F->ie, x); }
            cur = inst(&cur->clo, x);
        }
        if (cur->k != V_U || cur->pre) die("line %d: motive for %s must land in a universe, not %s", ms->line, datas[F->d0].name, show(c, cur));
        F->la = cur->lvl;
        Val *fib = eval(c->env, F->rt);
        for (int j = nb; j <= m0; j++) fib = vapp(fib, vvar(c->n + (j - nb)), 0);
        (void)fib;
        for (int i = 0; i < nb; i++) ctx_pop(c); }
    #undef TARGET_TYPE
    F->t = elim_type(F->d, F->la, 0, F->dl);   /* the eliminator's type (res_irr 0) */
    {   /* the indices and the target determine the parameters (metas), but they come last: check them first, for their
           constraints; the spine is then checked in order (their terms are taken from that pass) */
        int K = block_ncons(F->d), nbk = F->D->nblock, m = F->D->nidx;
        F->j = -1;
        if (F->n - F->ai == nbk + K + m + 1) { F->ie = F->pe; F->iv = xalloc((m + 1) * sizeof(Val *)); F->j = 0; F->nf = nbk + K; F->m0 = m; } }
    if (F->j >= 0) {
        for (F->j = 0; F->j < F->m0; F->j++) {
            MCALL(mpush_check(F->c, F->args[F->ai + F->nf + F->j], eval(F->ie, F->DV->itys[F->j])));
            F->iv[F->j] = eval(F->c->env, MTERM()); F->ie = env_push(F->ie, F->iv[F->j]);
        }
        {   Val *tt = mkval(V_DATA); tt->n = F->d; tt->lvl = F->dl;
            for (int i = 0; i < F->np; i++) vl_push(&tt->args, F->pvv[i], 1);
            for (int j = 0; j < F->m0; j++) vl_push(&tt->args, F->iv[j], 1);
            F->v = tt; }
        MCALL(mpush_check(F->c, F->args[F->n - 1], F->v));
    }
    {   Term *head = mk_ref_l(T_ELIM, F->d, F->dlt); Val *hty = eval(NULL, F->t);
        for (int i = 0; i < F->np; i++) { head = mk_app(head, F->pt[i], 1); hty = inst(&hty->clo, F->pvv[i]); }
        STerm **a = F->args + F->ai; int n = F->n - F->ai; Ctx *c = F->c;
        MTAIL(mpush_app_spine(c, a, n, head, hty)); }
    MFINISH
}
#undef C_
#undef A_

/* ---- systems ---- */
static void system_step(size_t off) {
    MSTART
    {   STerm *s = F->s; Term *t = mk_term(T_SYS, NULL, NULL, NULL, NULL); t->nbr = s->nbr; t->br = xalloc((s->nbr + 1) * sizeof(TBranch));
        F->t = t; F->psi = xalloc((s->nbr + 1) * sizeof(Val *)); F->v = vi(iv_zero()); }
    for (F->i = 0; F->i < F->s->nbr; F->i++) {
        MCALL(mpush_check(F->c, F->s->br[F->i].face, vinterval()));
        F->t->br[F->i].face = MTERM();
        F->psi[F->i] = eval(F->c->env, F->t->br[F->i].face);
        F->v = vi(iv_or(F->v->iv, F->psi[F->i]->iv));
    }
    if (!iv_eq(F->v->iv, F->ty->iv)) die("line %d: the system's faces cover %s, but its type demands %s", F->s->line, show(F->c, F->v), show(F->c, F->ty));
    for (F->i = 0; F->i < F->s->nbr; F->i++) {
        F->nf = faces_of(F->psi[F->i], &F->fs);
        if (F->nf == 0) die("line %d: the face %s of a system branch is never satisfied", F->s->br[F->i].face->line, show(F->c, F->psi[F->i]));
        F->t->br[F->i].body = NULL;
        for (F->j = 0; F->j < F->nf; F->j++) {
            F->rc = xalloc(sizeof(Ctx)); *F->rc = ctx_restrict(F->c, &F->fs[F->j]);   /* on the heap: the frame may move */
            F->x = F->tyat(&F->fs[F->j], F->data);
            MCALL(mpush_check(F->rc, F->s->br[F->i].body, F->x));
            if (!F->t->br[F->i].body) F->t->br[F->i].body = MTERM();
        }
    }
    /* overlapping branches must agree: both evaluated under the restriction to the common face */
    {   Ctx *c = F->c; STerm *s = F->s; Term *t = F->t; Val **psi = F->psi;
        for (int k = 0; k < s->nbr; k++) for (int l = k + 1; l < s->nbr; l++) {
            Face *fs; int nf = faces_of(vi(iv_and(psi[k]->iv, psi[l]->iv)), &fs);
            for (int i = 0; i < nf; i++) {
                Ctx rc = ctx_restrict(c, &fs[i]);
                if (!conv(c->n, eval(rc.env, t->br[k].body), eval(rc.env, t->br[l].body)))
                    die("line %d: system branches %d and %d disagree where their faces overlap", s->line, k + 1, l + 1);
            }
        } }
    MRETT(F->t);
    MFINISH
}

/* ---- terms ---- */
static void infer_step(size_t off) {
    MSTART
    switch (F->s->k) {   /* the kinds that call nothing: at once (no resume point inside this switch) */
    case S_VAR: {
        Ctx *c = F->c; STerm *s = F->s;
        for (int i = c->n - 1; i >= 0; i--)
            if (!strcmp(c->names[i], s->name)) {
                if (c->irrs[i] && !c->irrpos) die("line %d: '%s' is irrelevant (bound by .(%s : ..)); it may be used only in an irrelevant position (an irrelevant argument or component, a type, a proof of Empty)", s->line, s->name, s->name);
                eret_ty = c->tys[i]; MRETT(mk_var(c->n - 1 - i));
            }
        int id;
        if ((id = find_con(s->name)) >= 0) { LVal L; Term *lt = global_level(T_CON, id, &L); Val *ty = eval(NULL, con_at(id, L)->ty); eret_ty = ty; MRETT(mk_ref_l(T_CON, id, lt)); }
        if ((id = find_def(s->name)) >= 0) { LVal L; Term *lt = global_level(T_DEF, id, &L); Val *ty = def_ty_at(id, L); eret_ty = ty; MRETT(mk_ref_l(T_DEF, id, lt)); }
        if ((id = find_data(s->name)) >= 0) { LVal L; Term *lt = global_level(T_DATA, id, &L); Val *ty = eval(NULL, data_at(id, L)->ty); eret_ty = ty; MRETT(mk_ref_l(T_DATA, id, lt)); }
        die("line %d: unbound name '%s'", s->line, s->name);
    }
    case S_HOLE: {   /* a hole standing for a type: a meta in a universe at a fresh level */
        int l = lv_meta_new(); Val *U = vu_l(lv_meta(l)); Term *m = fresh_meta(F->c, U, F->s->line); eret_ty = U; MRETT(m);
    }
    case S_U:
        if (F->s->a) break;
        { Ctx *c = F->c; eret_ty = vu_l(lv_add(BASE_LEVEL(c), F->s->lvl + 1)); MRETT(mk_u_l(lv_add(BASE_LEVEL(c), F->s->lvl))); }   /* U n is U {L + n}, or U n when level-explicit */
    case S_LEVEL: eret_ty = vupre(0); MRETT(mk_term(T_LEVEL, NULL, NULL, NULL, NULL));   /* a pretype: no Kan structure, not inductive */
    case S_LZERO: eret_ty = vlevel(); MRETT(mk_lval(BASE_LEVEL(F->c)));   /* constants are relative to the hidden level unless level-explicit */
    case S_I: die("line %d: I is the type of interval variables; it is not itself a term of a universe", F->s->line);
    case S_I0: eret_ty = vinterval(); MRETT(mk_term(T_I0, NULL, NULL, NULL, NULL));
    case S_I1: eret_ty = vinterval(); MRETT(mk_term(T_I1, NULL, NULL, NULL, NULL));
    case S_NUM:
        die("line %d: the type of the numeral %llu is not determined here; a numeral is checked against a type shaped like the naturals (give it one: a binder, a let, an argument)", F->s->line, F->s->num);
    case S_LAM: die("line %d: cannot infer the type of a lambda; add an annotation", F->s->line);
    case S_SYS: die("line %d: cannot infer the type of a system; it must be checked against a Partial type", F->s->line);
    case S_PAIR: die("line %d: cannot infer the type of a pair; it must be checked against a Sigma type", F->s->line);
    case S_APP: case S_ELIM: case S_PATHP: case S_PARTIAL: case S_TRANSP: case S_HCOMP: case S_COMP: case S_SUB: case S_INS: case S_OUTS: case S_SIGMA: case S_FST: case S_SND: case S_GLUE: case S_GLUEEL: case S_UNGLUE:
        MBECOME(infer_app_step);
    default: break;
    }
    if (F->s->k == S_U) {   /* U {l}: a universe at a level expression */
        MCALL(mpush_check(F->c, F->s->a, vlevel())); F->t = MTERM();
        { LVal L = eval_level(F->c->env, F->t); Term *u = mk_u(0); u->a = F->t; eret_ty = vu_l(lv_add(L, 1)); MRETT(u); }
    }
    if (F->s->k == S_LSUC) { MCALL(mpush_check(F->c, F->s->a, vlevel())); { Term *r = mk_term(T_LSUC, MTERM(), NULL, NULL, NULL); r->n = 1; eret_ty = vlevel(); MRETT(r); } }
    if (F->s->k == S_LMAX) {
        MCALL(mpush_check(F->c, F->s->a, vlevel())); F->t = MTERM();
        MCALL(mpush_check(F->c, F->s->b, vlevel())); eret_ty = vlevel(); MRETT(mk_term(T_LMAX, F->t, MTERM(), NULL, NULL));
    }
    if (F->s->k == S_IAND || F->s->k == S_IOR) {
        MCALL(mpush_check(F->c, F->s->a, vinterval())); F->t = MTERM();
        MCALL(mpush_check(F->c, F->s->b, vinterval()));
        eret_ty = vinterval(); MRETT(mk_term(F->s->k == S_IAND ? T_IAND : T_IOR, F->t, MTERM(), NULL, NULL));
    }
    if (F->s->k == S_INEG) { MCALL(mpush_check(F->c, F->s->a, vinterval())); eret_ty = vinterval(); MRETT(mk_term(T_INEG, MTERM(), NULL, NULL, NULL)); }
    if (F->s->k == S_PI) {
        if (F->s->binders[0].ty->k == S_I) {   /* a function from the interval is a pretype: it has no Kan structure */
            if (F->s->binders[0].imp) die("line %d: an interval binder cannot be implicit", F->s->line);
            ctx_bind_i(F->c, F->s->binders[0].name);
            MCALL(mpush_sort(F->c, F->s->a, 0)); F->t = MTERM(); F->lb = eret_lvl;
            ctx_pop(F->c);
            eret_ty = vupre_l(F->lb);
            MRETT(mk_pi(F->s->binders[0].name, mk_term(T_INTERVAL, NULL, NULL, NULL, NULL), F->t, 0));
        }
        MCALL(mpush_sort(F->c, F->s->binders[0].ty, 0)); F->a = MTERM(); F->la = eret_lvl; F->pa = eret_pre;
        {   SBinder *b = &F->s->binders[0];
            Val *dv = eval(F->c->env, F->a);
            F->irr = F->a->k == T_LEVEL;   /* types are run-time codes, so every binder is relevant; levels are not */
            if (b->irrel) F->irr = 2;       /* .(x : A): proof-irrelevant - erased, not compared, usable only in irrelevant positions */
            ctx_bind_irr(F->c, b->name, dv, F->irr); }
        MCALL(mpush_sort(F->c, F->s->a, 0)); F->b = MTERM(); F->lb = eret_lvl; F->pb = eret_pre;
        ctx_pop(F->c);
        {   LVal l = lv_max(F->la, F->lb); SBinder *b = &F->s->binders[0];
            eret_ty = (F->pa || F->pb) ? vupre_l(l) : vu_l(l);   /* a function type from or into a pretype is a pretype */
            Term *t = mk_pi(b->name, F->a, F->b, F->irr); t->pre = F->pa; t->imp = b->imp; MRETT(t); }
    }
    if (F->s->k == S_LET) {
        MCALL(mpush_sort(F->c, F->s->a, 0)); F->a = MTERM();   /* a let may bind a line or a partial element */
        F->v = eval(F->c->env, F->a);
        MCALL(mpush_check(F->c, F->s->b, F->v)); F->b = MTERM();
        ctx_push(F->c, F->s->name, F->v, eval(F->c->env, F->b));
        MCALL(mpush_infer(F->c, F->s->c)); F->t = MTERM(); F->x = eret_ty;
        ctx_pop(F->c);
        eret_ty = F->x; MRETT(mk_let(F->s->name, F->a, F->b, F->t, 0));
    }
    MRETT(NULL);
    MFINISH
}

static void check_step(size_t off) {
    MSTART
    F->ty = force(F->ty);
    if (F->ty->k == V_DATA && datas[F->ty->n].ncons == 0) {   /* a proof of an empty type is an irrelevant position (absurdity from irrelevant hypotheses) */
        F->c->irrpos++; F->c->irrlen++;
        MCALL(epush(check1_step, F->c, F->s, F->ty));
        F->c->irrpos--; F->c->irrlen--; MRET(mret);
    }
    MBECOME(check1_step);
    MFINISH
}
static void check1_step(size_t off) {
    MSTART
    if (F->ty->k == V_PI && F->ty->imp && !(F->s->k == S_LAM && F->s->binders[0].imp)) {   /* an implicit function type: abstract over the argument */
        F->nm = xsprintf("{%s}", F->ty->name ? F->ty->name : "_");   /* not a name the program can write: no capture */
        ctx_bind(F->c, F->nm, F->ty->dom);
        MCALL(mpush_check(F->c, F->s, inst(&F->ty->clo, F->c->env->v)));
        ctx_pop(F->c);
        { Term *t = mk_lam(F->nm, MTERM(), F->ty->irr); t->imp = 1; MRETT(t); }
    }
    if (F->s->k == S_HOLE) MRETT(fresh_meta(F->c, F->ty, F->s->line));
    if (F->s->k == S_NUM) {
        if (is_word_type(F->c, F->ty)) {   /* a numeral at the word type: the pair (n, refl), its bound decided by the kernel */
            STerm *pr = xalloc(sizeof *pr), *r = xalloc(sizeof *r);
            r->k = S_VAR; r->name = "refl"; r->line = F->s->line;
            pr->k = S_PAIR; pr->line = F->s->line; pr->a = F->s; pr->b = r;
            Ctx *c = F->c; Val *ty = F->ty;
            MTAIL(mpush_check(c, pr, ty));
        }
        MRETT(check_numeral(F->c, F->s, F->ty));
    }
    if (F->s->k == S_LAM) {
        {   SBinder *b = &F->s->binders[0];
            if (b->imp && !(F->ty->k == V_PI && F->ty->imp)) die("line %d: the implicit lambda \\{%s} is checked against %s, not an implicit function type", F->s->line, b->name, show(F->c, F->ty)); }
        if (F->ty->k == V_PATHP) {
            ctx_bind_i(F->c, F->s->binders[0].name);
            F->i = F->c->n - 1;
            MCALL(mpush_check(F->c, F->s->a, vapp(F->ty->a, vivar(F->i), 0))); F->t = MTERM();
            {   Ctx *c = F->c; STerm *s = F->s; Val *ty = F->ty;
                Val *bv = eval(c->env, F->t);
                int var = F->i, v0 = 0, v1 = 1; Face f0 = { &var, &v0, 1 }, f1 = { &var, &v1, 1 };
                if (!conv(c->n, restrict_val(bv, &f0), ty->b)) die("line %d: the path's left endpoint is %s, expected %s", s->line, show(c, restrict_val(bv, &f0)), show(c, ty->b));
                if (!conv(c->n, restrict_val(bv, &f1), ty->c)) die("line %d: the path's right endpoint is %s, expected %s", s->line, show(c, restrict_val(bv, &f1)), show(c, ty->c));
                ctx_pop(c);
                Term *t = mk_lam(s->binders[0].name, F->t, 0); t->isi = 1; MRETT(t); }
        }
        if (F->ty->k != V_PI) die("line %d: lambda checked against non-function type %s", F->s->line, show(F->c, F->ty));
        if (F->ty->isi) {
            ctx_bind_i(F->c, F->s->binders[0].name);
            MCALL(mpush_check(F->c, F->s->a, inst(&F->ty->clo, vivar(F->c->n - 1))));
            ctx_pop(F->c);
            { Term *t = mk_lam(F->s->binders[0].name, MTERM(), 0); t->isi = 1; MRETT(t); }
        }
        ctx_bind_irr(F->c, F->s->binders[0].name, F->ty->dom, F->ty->irr);
        MCALL(mpush_check(F->c, F->s->a, inst(&F->ty->clo, vvar(F->c->n - 1))));
        ctx_pop(F->c);
        { Term *t = mk_lam(F->s->binders[0].name, MTERM(), F->ty->irr); t->imp = F->s->binders[0].imp; MRETT(t); }
    }
    if (F->s->k == S_LET) {
        MCALL(mpush_sort(F->c, F->s->a, 0)); F->a = MTERM();
        F->v = eval(F->c->env, F->a);
        MCALL(mpush_check(F->c, F->s->b, F->v)); F->b = MTERM();
        ctx_push(F->c, F->s->name, F->v, eval(F->c->env, F->b));
        MCALL(mpush_check(F->c, F->s->c, F->ty));
        ctx_pop(F->c);
        MRETT(mk_let(F->s->name, F->a, F->b, MTERM(), 0));
    }
    if (F->s->k == S_APP && F->s->a->k == S_INS) {   /* inS x : Sub A phi u  when x : A agrees with u on phi */
        if (F->ty->k != V_SUB) die("line %d: inS checked against %s, expected a Sub type", F->s->line, show(F->c, F->ty));
        MCALL(mpush_check(F->c, F->s->b, F->ty->a)); F->t = MTERM();
        {   Ctx *c = F->c; STerm *s = F->s; Val *ty = F->ty;
            Val *xv = eval(c->env, F->t);
            Face *fs; int nf = faces_of(ty->b, &fs);
            for (int i = 0; i < nf; i++) {
                Val *side = vsys_at(ty->c, &fs[i]);
                if (!side || !conv(c->n, restrict_val(xv, &fs[i]), side))
                    die("line %d: inS: the element does not agree with the subtype's sides on a face of %s", s->line, show(c, ty->b));
            }
            MRETT(mk_term(T_INS, F->t, NULL, NULL, NULL)); }
    }
    if (F->s->k == S_APP && F->s->a->k == S_APP && F->s->a->a->k == S_GLUEEL) {   /* glue ts a : Glue A phi Te */
        if (F->ty->k != V_GLUE) die("line %d: glue checked against %s, expected a Glue type", F->s->line, show(F->c, F->ty));
        if (F->s->a->b->k != S_SYS) die("line %d: the first argument of glue must be a system", F->s->a->b->line);
        MCALL(mpush_system_at(F->c, F->s->a->b, F->ty->b, glue_type_at, F->ty->c)); F->tst = MTERM();
        F->tsv = eval(F->c->env, F->tst);
        MCALL(mpush_check(F->c, F->s->b, F->ty->a)); F->a = MTERM();
        {   Ctx *c = F->c; STerm *s = F->s; Val *ty = F->ty;
            Val *av = eval(c->env, F->a);
            Face *fs; int nf = faces_of(ty->b, &fs);
            for (int i = 0; i < nf; i++) {
                Val *Te = vsys_at(ty->c, &fs[i]), *t = vsys_at(F->tsv, &fs[i]);
                if (!Te || !t) die("line %d: glue: the sides do not cover their face", s->line);
                Val *ea = vapp(vproj(vproj(Te, 2), 1), t, 0);
                if (!conv(c->n, restrict_val(av, &fs[i]), ea))
                    die("line %d: glue: the base does not agree with the equivalence applied to the sides on a face of %s", s->line, show(c, ty->b));
            }
            MRETT(mk_term(T_GLUEEL, F->tst, F->a, quote(c->n, ty), NULL)); }
    }
    if (F->s->k == S_PAIR) {
        if (F->ty->k != V_SIGMA) die("line %d: pair checked against %s, expected a Sigma type", F->s->line, show(F->c, F->ty));
        MCALL(mpush_check(F->c, F->s->a, F->ty->dom)); F->a = MTERM();
        if (F->ty->irr) { F->c->irrpos++; F->c->irrlen++; }
        MCALL(mpush_check(F->c, F->s->b, inst(&F->ty->clo, eval(F->c->env, F->a))));
        if (F->ty->irr) { F->c->irrpos--; F->c->irrlen--; }
        { Term *t = mk_term(T_PAIR, F->a, MTERM(), NULL, NULL); t->irr = F->ty->irr;
          if (is_word_type(F->c, F->ty)) t->n = 1;
          MRETT(t); }
    }
    if (F->s->k == S_SYS) {
        if (F->ty->k != V_PARTIAL) die("line %d: a system must be checked against a Partial type, not %s", F->s->line, show(F->c, F->ty));
        { Ctx *c = F->c; STerm *s = F->s; Val *phi = F->ty->a, *A = F->ty->b; MTAIL(mpush_system_at(c, s, phi, partial_type_at, A)); }
    }
    MCALL(mpush_infer(F->c, F->s)); F->t = MTERM(); F->got = force(eret_ty);
    {   Ctx *c = F->c; STerm *s = F->s; Val *ty = F->ty, *got = F->got; Term *t = F->t;
        while (got->k == V_PI && got->imp) {   /* trailing implicit arguments are supplied */
            Term *m = fresh_meta(c, got->dom, s->line);
            t = mk_app(t, m, got->irr); got = force(inst(&got->clo, eval(c->env, m)));
        }
        F->t = t;
        if (got->k == V_U && ty->k == V_NEU && ty->h == H_META) {
            /* a universe against a type not known yet: subtyping holds between sorts only, so the type is a universe of the same
               sort at a level to be determined; the level is a fresh level meta, bounded below by got's (the level store decides it) */
            Val *U = vu_l(lv_meta(lv_meta_new())); U->pre = got->pre;
            if (!conv(c->n, ty, U) && !c->irrlen) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
            if (lv_enforce_leq(got->lvl, U->lvl) != 1 && !c->irrlen) die("line %d: universe inconsistency: %s is not below %s", s->line, show(c, got), show(c, U));
        } else if (got->k == V_U && ty->k == V_U && got->pre <= ty->pre) {   /* cumulativity (a universe type is also a pretype): enforce got <= expected */
            int r = lv_enforce_leq(got->lvl, ty->lvl);
            if (!(r == 1 || c->irrlen)) {
                if (r < 0) die("line %d: level ambiguous: whether %s is below %s cannot be decided; write the level, f {l} ..", s->line, show(c, got), show(c, ty));
                die("line %d: universe inconsistency: %s is not below %s", s->line, show(c, got), show(c, ty));
            }
        } else {
            if (got->k == V_PARTIAL && ty->k != V_PARTIAL && iv_is_one(got->a->iv)) got = got->b;   /* a partial element on a face that holds is an element */
            if (!conv(c->n, got, ty) && !c->irrlen) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
        } }
    MCALL(mpush_resolve(F->c, 0));
    MRETT(F->t);
    MFINISH
}
#undef F

/* the C entries (declarations call these; each runs the machine to the result) */
static Term *check(Ctx *c, STerm *s, Val *ty) { mpush_check(c, s, ty); return (Term *)(void *)mrun(); }
static Term *check_type_sort(Ctx *c, STerm *s, LVal *lvl, int *pre) { mpush_sort(c, s, 0); Term *t = (Term *)(void *)mrun(); *lvl = eret_lvl; *pre = eret_pre; return t; }
static Term *check_type(Ctx *c, STerm *s, LVal *lvl) { mpush_sort(c, s, 1); Term *t = (Term *)(void *)mrun(); *lvl = eret_lvl; return t; }
static Term *check_interval(Ctx *c, STerm *s) { return check(c, s, vinterval()); }
static void resolve_deferred(Ctx *c, int all) { mpush_resolve(c, all); mrun(); }

/* ---- declarations ---- */

/* does the declared type (binder sugar folded into a Pi chain) bind a Level? */
static int declares_level(STerm *t) {
    for (; t && t->k == S_PI; t = t->a) if (t->binders[0].ty && t->binders[0].ty->k == S_LEVEL) return 1;
    return 0;
}

/* does the term mention the hidden level, other than as the level of an occurrence of a member of the block [lo, hi)? */
typedef struct { int lo, hi; } Range;
static int mhbb_pre(Term *t, int d, void *ctx) {
    Range *r = ctx; (void)d;
    switch (t->k) {
    case T_LVAL: return lv_mentions_hidden(t->lvl) ? 1 : -1;
    case T_DATA: case T_ELIM: case T_NUM: if (t->n >= r->lo && t->n < r->hi) return -1; term_any_push(t->a, d); return 2;
    case T_CON: if (cons[t->n].data >= r->lo && cons[t->n].data < r->hi) return -1; term_any_push(t->a, d); return 2;
    default: return 0;
    }
}
static int mentions_hidden_but_block(Term *t, int lo, int hi) { Range r = { lo, hi }; return term_any(t, 0, 1, mhbb_pre, &r); }
static LVal lv_subst_metas(LVal l, LVal *sol, int m0) {
    for (int i = 0; i < l.n; i++) if (l.t[i].meta && l.t[i].var >= m0) { int id = l.t[i].var; l = lv_subst_meta(l, id, sol[id - m0]); i = -1; }
    return l;
}
/* the metas minted since m0 are solved at their lower bounds and replaced in the given terms; the store is rolled back */
static void solve_metas(const char *what, int line, int m0, LMark mark, Term **terms, int nterms, LVal *lvls, int nlvls) {
    int n = lstore_nmetas() - m0;
    if (n > 0) {
        LVal *sol = xalloc((n + 1) * sizeof(LVal)); int bad;
        if (!lstore_solve(m0, sol, &bad)) die("line %d: in %s, the level ?%d cannot be solved: %s fails at its lower bound; write the level explicitly", line, what, bad, lstore_bad_constraint());
        for (int i = 0; i < nterms; i++) if (terms[i]) terms[i] = subst_metas(terms[i], sol, m0);
        for (int i = 0; i < nlvls; i++) lvls[i] = lv_subst_metas(lvls[i], sol, m0);
    }
    lstore_rollback(mark);
}

/* does t mention a data type of the block [lo, hi)? */
static int mrange_pre(Term *t, int d, void *ctx) {
    Range *r = ctx; (void)d;
    switch (t->k) {
    case T_DATA: return t->n >= r->lo && t->n < r->hi ? 1 : -1;
    case T_VAR: case T_U: case T_DEF: case T_CON: case T_NUM: case T_ELIM: case T_INTERVAL: case T_I0: case T_I1: return -1;
    default: return 0;
    }
}
static int mentions_range(Term *t, int lo, int hi) { Range r = { lo, hi }; return term_any(t, 0, 1, mrange_pre, &r); }
static int data_spine(Term *t, int d, int pbase, Term ***idx, int *nidx);
/* is t an application spine of some member of the block [lo, hi)? which member in *which */
static int data_spine_any(Term *t, int lo, int hi, int pbase, Term ***idx, int *nidx, int *which) {
    Term *w = t; while (w->k == T_APP) w = w->a;
    if (w->k != T_DATA || w->n < lo || w->n >= hi) return 0;
    *which = w->n; return data_spine(t, w->n, pbase, idx, nidx);
}
/* is t an application spine  D p_0 .. p_{np-1} idx..  with the params being the variables at pbase?  returns index terms */
static int data_spine(Term *t, int d, int pbase, Term ***idx, int *nidx) {
    Data *D = &datas[d];
    int nargs = 0; Term *w = t;
    while (w->k == T_APP) { nargs++; w = w->a; }
    if (w->k != T_DATA || w->n != d) return 0;
    if (nargs != D->nparams + D->nidx) die("data type %s applied to %d arguments, expected %d", D->name, nargs, D->nparams + D->nidx);
    Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
    for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    for (int i = 0; i < D->nparams; i++)
        if (args[i]->k != T_VAR || args[i]->n != pbase + D->nparams - 1 - i)
            die("constructor of %s must return the data type applied to its own parameters", D->name);
    *idx = args + D->nparams; *nidx = D->nidx;
    return 1;
}


/* does t mention the variable idx other than as a parameter argument of a constructor (which transport rewrites anyway)? */
static int mess_pre(Term *t, int d, void *ctx) {
    int idx = *(int *)ctx + d;
    switch (t->k) {
    case T_VAR: return t->n == idx ? 1 : -1;
    case T_APP: {
        int nargs = 0; Term *w = t;
        while (w->k == T_APP) { nargs++; w = w->a; }
        if (w->k == T_CON) {   /* only the arguments after the parameters */
            int np = datas[cons[w->n].data].nparams;
            Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
            for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
            for (int i = nargs - 1; i >= np; i--) term_any_push(args[i], d);
            return 2;
        }
        term_any_push(t->b, d); term_any_push(t->a, d); return 2;
    }
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return -1;
    default: return 0;
    }
}
/* does t mention the variable idx other than as a parameter argument of a constructor (which transport rewrites anyway)? */
static int mentions_essentially(Term *t, int idx) { return term_any(t, 0, 0, mess_pre, &idx); }
/* The boundary grammar (CHM18, 3.2): an element of D in a boundary is a recursive argument of the constructor, a
   recursive path argument applied to an interval, a recursive argument of function type applied, or an earlier
   constructor of D applied to the parameters, to arguments by this grammar and to intervals. Nothing else stands for
   an element of D (no Kan operation, eliminator, definition or let), and no recursive argument appears at a position
   whose type is not D: the eliminator images recursive arguments by their induction hypotheses, which inhabit the
   motive, so a recursive argument at any other position would give the method an ill-typed boundary.
   Context of a boundary: [params(np), args(r), intervals(nint)] (+ depth under binders opened inside it). */
typedef struct { Con *C; int np, r, nint, line; int dt; } BGram;   /* dt: the data type the position ranges over */
static const char *bg_D(BGram *g) { return datas[g->dt].name; }
/* a variable standing for a recursive argument of the constructor: its ordinal in *j */
static int bg_rec_var_any(BGram *g, Term *t, int depth, int *j) {   /* a recursive argument, of any member */
    if (t->k != T_VAR || t->n < depth) return 0;
    int idx = t->n - depth;
    if (idx < g->nint || idx >= g->nint + g->r) return 0;
    *j = g->r - 1 - (idx - g->nint);
    return g->C->args[*j].isrec || g->C->args[*j].isrecpath;
}
static int bg_rec_var(BGram *g, Term *t, int depth, int *j) {   /* a recursive argument of the position's member */
    return bg_rec_var_any(g, t, depth, j) && g->C->args[*j].rec == g->dt;
}
/* a position whose type is not D: no recursive argument inside */
static int bg_no_rec_pre(Term *t, int depth, void *ctx) {
    BGram *g = ctx; int j;
    if (bg_rec_var_any(g, t, depth, &j))
        die("line %d: the boundary of %s uses the recursive argument %s at a position whose type is not %s; a recursive argument may only stand for an element of %s (its image under the eliminator is an induction hypothesis)",
            g->line, g->C->name, g->C->args[j].name, bg_D(g), bg_D(g));
    return 0;
}
static void bg_no_rec(BGram *g, Term *t, int depth) { term_any(t, depth, 0, bg_no_rec_pre, g); }
/* the boundary grammar's positions: an element of D, a path in D, or a position with no recursive argument inside; a
   work list (the memory layer's stack) visited in the order the recursion took */
enum { BG_ELEM, BG_PATH, BG_NOREC, BG_BADFN };   /* BG_BADFN: the error the recursion reported at that point of its walk */
typedef struct { int k; BGram g; Term *t; int depth; Con *Cp; int q; } BGItem;
static Stack bgst = { NULL, 0, 0, sizeof(BGItem) };
static void bg_push(int k, BGram *g, Term *t, int depth) { BGItem it = { k, *g, t, depth, NULL, 0 }; STACK_PUSH(&bgst, BGItem, it); }
static void bg_reverse(size_t from) {   /* the items pushed since from in visiting order: reversed, so the first is on top */
    for (size_t i = from, j = bgst.n; i + 1 < j; i++, j--) { BGItem x = STACK_AT(&bgst, BGItem, i); STACK_AT(&bgst, BGItem, i) = STACK_AT(&bgst, BGItem, j - 1); STACK_AT(&bgst, BGItem, j - 1) = x; }
}
static void bg_step(BGItem *it) {
    BGram *g = &it->g; Term *t = it->t; int depth = it->depth, j;
    if (it->k == BG_NOREC) { bg_no_rec(g, t, depth); return; }
    if (it->k == BG_BADFN)
        die("line %d: the boundary or index of %s: the argument %s of %s (a function into %s) must be an abstraction or a recursive argument of that type", g->line, g->C->name, it->Cp->args[it->q].name, it->Cp->name, bg_D(g));
    if (it->k == BG_PATH) {   /* a path in D: a recursive path argument, or an abstraction over an interval whose body is an element */
        if (bg_rec_var(g, t, depth, &j) && g->C->args[j].isrecpath) return;
        if (t->k == T_LAM && t->isi) { bg_push(BG_ELEM, g, t->a, depth + 1); return; }
        die("line %d: the boundary of %s: a path in %s must be a recursive path argument or an abstraction over an interval", g->line, g->C->name, bg_D(g));
    }
    /* an element of D */
    if (bg_rec_var_any(g, t, depth, &j) && g->C->args[j].rec != g->dt)
        die("line %d: the boundary or index of %s: the recursive argument %s is an element of %s, not of %s", g->line, g->C->name, g->C->args[j].name, datas[g->C->args[j].rec].name, bg_D(g));
    if (bg_rec_var(g, t, depth, &j)) {
        if (g->C->args[j].isrec && g->C->args[j].npi == 0) return;
        die("line %d: the boundary of %s: the recursive argument %s is not an element of %s; apply it", g->line, g->C->name, g->C->args[j].name, bg_D(g));
    }
    if (t->k == T_PAPP) {   /* a recursive path argument at an interval */
        if (bg_rec_var(g, t->a, depth, &j) && g->C->args[j].isrecpath) { bg_push(BG_NOREC, g, t->b, depth); return; }
        die("line %d: the boundary of %s: only a recursive path argument may be applied to an interval here", g->line, g->C->name);
    }
    int nargs = 0; Term *w = t;
    while (w->k == T_APP) { nargs++; w = w->a; }
    size_t from = bgst.n;
    if (bg_rec_var(g, w, depth, &j)) {   /* a recursive argument of function type, applied */
        if (!g->C->args[j].isrec || nargs != g->C->args[j].npi)
            die("line %d: the boundary of %s: the recursive argument %s must be applied to exactly its %d argument%s", g->line, g->C->name, g->C->args[j].name, g->C->args[j].npi, g->C->args[j].npi == 1 ? "" : "s");
        for (Term *x = t; x->k == T_APP; x = x->a) bg_push(BG_NOREC, g, x->b, depth);
        bg_reverse(from); return;
    }
    if (w->k != T_CON || cons[w->n].data != g->dt)
        die("line %d: the boundary or index of %s: an element of %s here must be a recursive argument or an earlier constructor applied; a Kan operation, eliminator, definition or let cannot stand for one (CHM18 3.2)",
            g->line, g->C->name, bg_D(g));
    Con *Cp = &cons[w->n];
    if (Cp->bord >= g->C->bord) die("line %d: the boundary or index of %s uses the later constructor %s; only earlier constructors may appear", g->line, g->C->name, Cp->name);
    if (nargs != g->np + Cp->nargs + Cp->nint)
        die("line %d: the boundary of %s applies %s to %d arguments, expected %d", g->line, g->C->name, Cp->name, nargs, g->np + Cp->nargs + Cp->nint);
    Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
    for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    for (int i = 0; i < g->np; i++) bg_push(BG_NOREC, g, args[i], depth);
    for (int q = 0; q < Cp->nargs; q++) {
        Term *a = args[g->np + q]; ConArg *A = &Cp->args[q];
        if (!(A->isrec || A->isrecpath)) { bg_push(BG_NOREC, g, a, depth); continue; }
        BGram g2 = *g; g2.dt = A->rec;   /* the position ranges over the member of the recursive occurrence */
        if (A->isrecpath) bg_push(BG_PATH, &g2, a, depth);
        else if (A->npi == 0) bg_push(BG_ELEM, &g2, a, depth);
        else {   /* a function into the member: a recursive argument of that function type, or an abstraction whose body is an element */
            int jj;
            if (bg_rec_var(&g2, a, depth, &jj) && g->C->args[jj].isrec && g->C->args[jj].npi == A->npi) continue;
            Term *b = a; int k = 0;
            while (k < A->npi && b->k == T_LAM && !b->isi) { b = b->a; k++; }
            if (k < A->npi) {   /* the recursion reported this after the earlier arguments' positions: so does the work list */
                BGItem bad = { BG_BADFN, g2, a, depth, Cp, q }; STACK_PUSH(&bgst, BGItem, bad); continue;
            }
            bg_push(BG_ELEM, &g2, b, depth + k);
        }
    }
    for (int q = 0; q < Cp->nint; q++) bg_push(BG_NOREC, g, args[g->np + Cp->nargs + q], depth);
    bg_reverse(from);
}
static void bg_run(int k, BGram *g, Term *t, int depth) {
    size_t base = bgst.n;
    bg_push(k, g, t, depth);
    while (bgst.n > base) {
        BGItem it = STACK_POP(&bgst, BGItem);
        bg_step(&it);
    }
}
static void bg_elem(BGram *g, Term *t, int depth) { bg_run(BG_ELEM, g, t, depth); }

/* a block of data types declared together (a lone data type is a block of one), sharing the parameters:
   the members' signatures first, in order (each may use the earlier members' type formers), then the constructors in
   order (their types may use every member; boundaries and indices only earlier constructors); strict positivity is
   checked across the block; every member's eliminator takes the block's motives and methods. */
static void elab_block(SDecl **ms, int n, SBinder *params, int nparams, int line) {
    for (int i = 0; i < n; i++) check_fresh(ms[i]->name, ms[i]->line);
    Ctx c = {0};
    for (int i = 0; i < nparams; i++) if (params[i].ty->k == S_LEVEL) c.abs = 1;   /* level-explicit: absolute constants */
    for (int i = 0; i < nparams; i++) if (params[i].imp) die("line %d: data %s: a parameter is always explicit in the type former (it is implicit in the constructors)", line, ms[0]->name);
    int m0 = lstore_nmetas(); LMark mark = lstore_mark(); int mm0 = ntmetas;
    Term **ptys = xalloc((nparams + 1) * sizeof(Term *));
    for (int i = 0; i < nparams; i++) {
        LVal l; int p; ptys[i] = check_type_sort(&c, params[i].ty, &l, &p);   /* a parameter may be a Level */
        if (p && ptys[i]->k != T_LEVEL) die("line %d: parameter %s of data %s: a type in a universe (or Level) is needed, but the term is a pretype", line, params[i].name, ms[0]->name);
        ctx_bind(&c, params[i].name, eval(c.env, ptys[i]));
    }
    int d0 = ndatas;
    datas = rrealloc(datas, (ndatas + n) * sizeof(Data));
    for (int i = 0; i < n; i++) {
        SDecl *s = ms[i];
        Data D = {0}; D.name = s->name; D.line = s->line; D.seq = decl_seq++; D.nparams = nparams; D.ptys = ptys;
        LVal l; Term *ity = check_type(&c, s->ty, &l);
        Term *w = ity; int m = 0;
        for (Term *x = ity; x->k == T_PI; x = x->b) m++;
        D.nidx = m; D.itys = xalloc((m + 1) * sizeof(Term *));
        for (int j = 0; j < m; j++) { D.itys[j] = w->a; w = w->b; }
        if (w->k != T_U) die("line %d: the type of data %s must end in a universe", s->line, s->name);
        {   /* the universe sits under the index binders: read its level there, and it may not depend on an index */
            Env *ie = c.env; for (int j = 0; j < m; j++) ie = env_push(ie, vvar(c.n + j));
            D.lvl = w->a ? eval_level(ie, w->a) : lv_const(w->n);
            for (int q = 0; q < D.lvl.n; q++) if (!D.lvl.t[q].meta && D.lvl.t[q].var >= c.n) die("line %d: the universe level of data %s may not depend on an index", s->line, s->name);
        }
        D.idxrec = xalloc((m + 1) * sizeof(int)); D.nimg = 0;
        for (int q = 0; q < m; q++) {   /* an index ranging over an earlier member: the eliminator images it */
            Term **ix; int nix, which = -1; D.idxrec[q] = -1;
            if (!mentions_range(D.itys[q], d0, ndatas)) continue;
            if (!data_spine_any(D.itys[q], d0, ndatas, q, &ix, &nix, &which))
                die("line %d: data %s: an index type mentioning a member of the block must be that member applied to the parameters", s->line, s->name);
            if (nix > 0) die("line %d: data %s: an index of type %s applied to indices is not supported yet", s->line, s->name, datas[which].name);
            D.idxrec[q] = which; D.nimg++;
        }
        Term *full = ity;
        for (int q = nparams - 1; q >= 0; q--) full = mk_pi(params[q].name, ptys[q], full, 0);
        /* indices are run-time components of the type's code: hcomp is a formal element of an indexed family and its
           elimination applies the motive to the indices read off the code */
        { Term *x = ity; for (int j = 0; j < m; j++) { x->irr = 0; x = x->b; } }
        D.ty = full;
        D.block = d0; D.nblock = n; D.bpos = i;
        D.poly = 1;   /* provisionally polymorphic: the members' own occurrences carry the hidden level */
        datas[ndatas++] = D;
    }
    cur_data = d0; cur_data_hi = d0 + n;
    int bord = 0;
    for (int i = 0; i < n; i++) {
      SDecl *s = ms[i]; int d = d0 + i;
      datas[d].bcons0 = bord;
      for (int ci = 0; ci < s->ncons; ci++) {
        SCon *sc = &s->cons[ci];
        check_fresh(sc->name, sc->line);
        LVal lcv; int pc; Term *cty = check_type_sort(&c, sc->ty, &lcv, &pc);   /* a pretype only through its interval binders */
        if (lv_enforce_leq(lcv, datas[d].lvl) != 1) die("line %d: constructor %s : its type lives above the universe of data %s", sc->line, sc->name, s->name);
        Con C = {0}; C.name = sc->name; C.data = d; C.ci = ci; C.bord = bord++; C.line = sc->line;
        int r = 0; for (Term *x = cty; x->k == T_PI && x->a->k != T_INTERVAL; x = x->b) r++;
        C.args = xalloc((r + 1) * sizeof(ConArg)); C.nargs = r;
        Term *x = cty;
        for (int j = 0; j < r; j++) {
            ConArg *A = &C.args[j];
            if (x->pre) die("line %d: constructor %s: the argument %s is a pretype; constructor arguments must be types in a universe", sc->line, sc->name, x->name);
            A->name = x->name; A->ty = x->a; A->irr = x->irr; A->imp = x->imp;
            /* a recursive path argument: Path (D' params) px py, D' a member of the block */
            if (A->ty->k == T_PATHP && A->ty->a->k == T_LAM) {
                Term **idx; int nidx, rd = -1;
                if (mentions_range(A->ty->a->a, d0, d0 + n)) {
                    if (!data_spine_any(A->ty->a->a, d0, d0 + n, j + 1, &idx, &nidx, &rd))
                        die("line %d: constructor %s: a path argument must be a path in %s itself (or a member of its block)", sc->line, sc->name, s->name);
                    if (term_mentions_var(A->ty->a->a, 0)) die("line %d: constructor %s: a path argument's line must be constant", sc->line, sc->name);
                    A->isrecpath = 1; A->rec = rd; A->px = A->ty->b; A->py = A->ty->c; C.nrec++;
                    A->nidx = nidx; A->idx = xalloc((nidx + 1) * sizeof(Term *));
                    for (int q = 0; q < nidx; q++) A->idx[q] = subst_term(idx[q], 0, mk_term(T_I0, NULL, NULL, NULL, NULL));   /* drop the unused binder */
                    x = x->b; continue;
                }
            }
            /* strict positivity, across the block */
            Term *y = A->ty; int q = 0;
            while (y->k == T_PI) {
                if (mentions_range(y->a, d0, d0 + n)) die("line %d: constructor %s is not strictly positive in %s", sc->line, sc->name, s->name);
                y = y->b; q++;
            }
            Term **idx; int nidx, rd = -1;
            if (mentions_range(y, d0, d0 + n)) {
                if (!data_spine_any(y, d0, d0 + n, q + j, &idx, &nidx, &rd)) die("line %d: constructor %s is not strictly positive in %s", sc->line, sc->name, s->name);
                A->isrec = 1; A->rec = rd; A->npi = q; A->idx = idx; A->nidx = nidx; C.nrec++;
            }
            x = x->b;
        }
        /* interval binders of a path constructor */
        int nint = 0;
        for (; x->k == T_PI; x = x->b) { if (x->a->k != T_INTERVAL) die("line %d: constructor %s: interval binders must come last", sc->line, sc->name); nint++; }
        C.nint = nint;
        Term **ridx; int nridx;
        if (!data_spine(x, d, r + nint, &ridx, &nridx)) die("line %d: constructor %s must return %s", sc->line, sc->name, s->name);
        C.ridx = ridx;
        for (int j = 0; j < nridx; j++) for (int q = 0; q < nint; q++)
            if (term_mentions_var(ridx[j], nint - 1 - q)) die("line %d: path constructor %s: an index may not vary along the interval", sc->line, sc->name);
        /* an index ranging over a member is imaged by the eliminator: it must be in the constructor language */
        for (int q = 0; q < nridx; q++) if (datas[d].idxrec[q] >= 0) { BGram g = { &C, nparams, r, nint, sc->line, datas[d].idxrec[q] }; bg_elem(&g, ridx[q], 0); }
        for (int j = 0; j < r; j++) {
            ConArg *A = &C.args[j];
            if (!(A->isrec || A->isrecpath)) continue;
            for (int q = 0; q < A->nidx; q++) if (datas[A->rec].idxrec[q] >= 0) { BGram g = { &C, nparams, j, 0, sc->line, datas[A->rec].idxrec[q] }; bg_elem(&g, A->idx[q], A->isrec ? A->npi : 0); }
        }
        if (sc->boundary && nint == 0) die("line %d: constructor %s has a boundary but no interval binders", sc->line, sc->name);
        if (sc->boundary) {   /* the boundary: a system of elements of D params under [params, args, intervals] */
            Ctx bc = c; bc.names = xalloc((c.n + r + nint + 1) * sizeof(char *)); bc.tys = xalloc((c.n + r + nint + 1) * sizeof(Val *));
            memcpy(bc.names, c.names, c.n * sizeof(char *)); memcpy(bc.tys, c.tys, c.n * sizeof(Val *)); bc.cap = c.n + r + nint + 1;
            Term *w = cty;
            for (int j = 0; j < r; j++) { ctx_bind(&bc, w->name, eval(bc.env, w->a)); w = w->b; }
            for (int q = 0; q < nint; q++) { ctx_bind_i(&bc, w->name); w = w->b; }
            IVal cover = iv_zero();
            for (int i2 = 0; i2 < sc->boundary->nbr; i2++) { Term *f = check_interval(&bc, sc->boundary->br[i2].face); cover = iv_or(cover, eval(bc.env, f)->iv); }
            Val *Dv = mkval(V_DATA); Dv->n = d; Dv->lvl = lv_hidden();
            for (int i2 = 0; i2 < nparams; i2++) vl_push(&Dv->args, vvar(i2), 0);
            for (int j = 0; j < nridx; j++) vl_push(&Dv->args, eval(bc.env, ridx[j]), 1);   /* the boundary lives at the constructor's own index */
            Val *pty = mkval(V_PARTIAL); pty->a = vi(cover); pty->b = Dv;
            C.boundary = zonk(check(&bc, sc->boundary, pty));   /* its implicit arguments are determined by the constructor's own type */
            {   /* the boundary must be in the constructor language (CHM18): checked after typing, at the declaration */
                BGram g = { &C, nparams, r, nint, sc->line, d };
                for (int i2 = 0; i2 < C.boundary->nbr; i2++) bg_elem(&g, C.boundary->br[i2].body, 0);
            }
            /* does the boundary depend on the parameters beyond passing them to constructors? (then transport must correct it) */
            for (int i2 = 0; i2 < C.boundary->nbr; i2++)
                for (int p = 0; p < nparams; p++) if (mentions_essentially(C.boundary->br[i2].body, r + nint + (nparams - 1 - p))) C.bparams = 1;
            if (nint == 1) {
                Term *v0 = mk_term(T_I0, NULL, NULL, NULL, NULL), *v1 = mk_term(T_I1, NULL, NULL, NULL, NULL); int has0 = 0, has1 = 0;
                for (int i2 = 0; i2 < C.boundary->nbr; i2++) {
                    if (iv_is_one(eval(NULL, subst_term(C.boundary->br[i2].face, 0, v0))->iv)) has0 = 1;
                    if (iv_is_one(eval(NULL, subst_term(C.boundary->br[i2].face, 0, v1))->iv)) has1 = 1;
                }
                C.pathmethod = has0 && has1;
            }
        }
        if (nint > 0) datas[d].hit = 1;
        Term *closed = cty;
        for (int q = nparams - 1; q >= 0; q--) { closed = mk_pi(params[q].name, ptys[q], closed, !C.bparams); closed->imp = 1; }   /* the parameters are implicit */
        C.ty = closed;
        int cid = ncons;
        cons = rrealloc(cons, (ncons + 1) * sizeof(Con));
        cons[ncons++] = C;
        Data *DD = &datas[d];
        DD->cons = rrealloc(DD->cons, (DD->ncons + 1) * sizeof(int));
        DD->cons[DD->ncons++] = cid;
      }
    }
    cur_data = -1; cur_data_hi = -1;
    /* every term of the block, for solving the metas and deciding polymorphism */
    int nt = 0, cap = 64; Term **ts = rcalloc(cap, sizeof(Term *)); Term ***slots = rcalloc(cap, sizeof(Term **)); int *isty = rcalloc(cap, sizeof(int));   /* grown below: plain blocks of the memory layer, not the arena */
    #define SLOT(p) do { if (nt == cap) { cap *= 2; ts = rrealloc(ts, cap * sizeof(Term *)); slots = rrealloc(slots, cap * sizeof(Term **)); isty = rrealloc(isty, cap * sizeof(int)); } slots[nt] = &(p); isty[nt] = 0; ts[nt++] = (p); } while (0)
    for (int i = 0; i < nparams; i++) SLOT(ptys[i]);
    for (int i = 0; i < n; i++) {
        Data *DD = &datas[d0 + i];
        for (int j = 0; j < DD->nidx; j++) SLOT(DD->itys[j]);
        SLOT(DD->ty); isty[nt - 1] = 1;   /* a member's own universe does not decide polymorphism */
        for (int ci = 0; ci < DD->ncons; ci++) {
            Con *C = &cons[DD->cons[ci]];
            SLOT(C->ty); SLOT(C->boundary);
            for (int j = 0; j < C->nargs; j++) { SLOT(C->args[j].ty); SLOT(C->args[j].px); SLOT(C->args[j].py); for (int q = 0; q < C->args[j].nidx; q++) SLOT(C->args[j].idx[q]); }
            for (int j = 0; j < DD->nidx; j++) SLOT(C->ridx[j]);
        }
    }
    #undef SLOT
    resolve_deferred(&c, 0); metas_finish(ms[0]->name, line, mm0); resolve_deferred(&c, 1);
    for (int i = 0; i < nt; i++) ts[i] = zonk(ts[i]);
    LVal *lvs = xalloc((n + 1) * sizeof(LVal)); for (int i = 0; i < n; i++) lvs[i] = datas[d0 + i].lvl;
    int hlo, hhi; lv_hidden_bounds(&hlo, &hhi);   /* before the rollback (M20, as in elab_def) */
    solve_metas(ms[0]->name, line, m0, mark, ts, nt, lvs, n);
    for (int i = 0; i < nt; i++) *slots[i] = ts[i];
    for (int i = 0; i < n; i++) datas[d0 + i].lvl = lvs[i];
    /* polymorphic if some parameter, index or constructor mentions the hidden level (the members' own universes do not
       count, nor do the levels of their own occurrences, which are at the hidden level by construction) */
    int poly = 0;
    for (int i = 0; i < nt; i++) if (!isty[i] && mentions_hidden_but_block(ts[i], d0, d0 + n)) poly = 1;
    if (hhi >= 0 || hlo > 0) poly = 0;   /* M20: a bounded hidden level: monomorphic at the lower bound */
    if (!poly) {   /* not polymorphic: the hidden level is the lower bound (0 unless the store says otherwise) */
        for (int i = 0; i < nt; i++) *slots[i] = subst_hidden(ts[i], lv_const(hlo));
        for (int i = 0; i < n; i++) datas[d0 + i].lvl = lv_subst(datas[d0 + i].lvl, -1, lv_const(hlo));
    }
    for (int i = 0; i < n; i++) datas[d0 + i].poly = poly;
    /* every higher inductive type must have an induction principle: build it now, so that a boundary the
       eliminator cannot image is refused at the declaration rather than at the first elimination */
    for (int i = 0; i < n; i++) if (datas[d0 + i].hit) (void)elim_type(d0 + i, datas[d0 + i].lvl, 0, poly ? lv_hidden() : lv_const(0));
}
static void elab_data(SDecl *s) { elab_block(&s, 1, s->params, s->nparams, s->line); }

static void elab_def(SDecl *s) {
    check_fresh(s->name, s->line);
    Ctx c = {0};
    c.abs = declares_level(s->ty);   /* level-explicit: absolute constants */
    int m0 = lstore_nmetas(); LMark mark = lstore_mark(); int mm0 = ntmetas;
    LVal l; int p; Term *ty = check_type_sort(&c, s->ty, &l, &p);   /* a definition may be a line, a partial element, a filler */
    Val *vty = eval(NULL, ty);
    int typelike = is_type_like(0, vty);
    if (typelike) c.irrpos++;   /* the body of a type-like definition is a type */
    Term *val = check(&c, s->val, vty);
    if (typelike) c.irrpos--;
    resolve_deferred(&c, 0); metas_finish(s->name, s->line, mm0); resolve_deferred(&c, 1);
    Term *ts[2] = { zonk(ty), zonk(val) };
    int hlo, hhi; lv_hidden_bounds(&hlo, &hhi);   /* before the store is rolled back: is the hidden level bounded? */
    solve_metas(s->name, s->line, m0, mark, ts, 2, NULL, 0);
    ty = ts[0]; val = ts[1];
    if (hhi >= 0 || hlo > 0) {   /* M20: a bounded hidden level is not uniformly liftable (Cover : S1 -> U pinned to 0 by ua^0 was lifted to U 1): monomorphic at the lower bound */
        ty = subst_hidden(ty, lv_const(hlo)); val = subst_hidden(val, lv_const(hlo));
    }
    Def D = {0}; D.name = s->name; D.line = s->line; D.seq = decl_seq++;
    D.poly = term_mentions_hidden(ty) || term_mentions_hidden(val);
    if (!D.poly) { ty = subst_hidden(ty, lv_const(0)); val = subst_hidden(val, lv_const(0)); }
    D.ty = ty; D.val = val;
    D.vty = eval(NULL, D.poly ? subst_hidden(ty, lv_const(0)) : ty);
    D.vval = eval(NULL, D.poly ? subst_hidden(val, lv_const(0)) : val);
    D.irr = is_type_like(0, D.vty);
    if (s->isword) {   /* M16a: the word type, or an operation on it (registered at level 0; a type is polymorphic like any other) */
        if (D.vty->k == V_U) {
            if (word_type >= 0) die("line %d: word %s: the word type is already declared (%s)", s->line, s->name, defs[word_type].name);
            Val *w = force(D.vval); int zi, si;
            Val *dom = w->k == V_SIGMA ? force(w->dom) : NULL;
            if (!dom || !w->irr || dom->k != V_DATA || dom->args.n != 0 || !peano_shape(dom->n, &zi, &si))
                die("line %d: word %s: the word type must be Sigma D .(P) for a data type D shaped like the naturals and an irrelevant P", s->line, s->name);
            D.isword = 1; word_type = ndefs; word_nat = dom->n;
        } else {
            int code = wordop_code(s->name);
            if (!code) die("line %d: word %s: not a run-time word primitive (wadd wsub wmul wand wor wxor wshl wshr weq wlt waddc wsubb wmull wdivmod)", s->line, s->name);
            if (word_type < 0) die("line %d: word %s: declare the word type first (word Word : U := Sigma D .(P))", s->line, s->name);
            check_wordop_type(code, D.vty, s->line, s->name);
            D.wordop = code;
        }
    }
    if (s->isnative) {   /* computes by a kernel primitive on literals, by its body otherwise */
        int code = native_code(s->name);
        if (!code) die("line %d: native %s: not a kernel primitive (add sub mul div mod pow beq blt ble)", s->line, s->name);
        if (D.poly) die("line %d: native %s: a native definition takes no level", s->line, s->name);
        int d = native_type_data(D.vty, s->line, s->name);
        D.native = code; D.vfallback = D.vval; D.vval = native_wrapper(code, d, D.vfallback, ndefs);
    }
    defs = rrealloc(defs, (ndefs + 1) * sizeof(Def));
    defs[ndefs++] = D;
}

void elab_program(SDecl *decls) {
    for (SDecl *s = decls; s; s = s->next) {
        cur_decl_name = s->name;
        if (s->isdata == 2) elab_block(s->members, s->nmembers, s->params, s->nparams, s->line);
        else if (s->isdata) elab_data(s); else elab_def(s);
    }
    cur_decl_name = NULL;
}
