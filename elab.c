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

typedef struct { const char **names; Val **tys; int n, cap; Env *env; int abs; } Ctx;
/* abs: the global being elaborated declares Level binders, so its constant levels are absolute (U is U 0);
   otherwise constants are relative to the hidden level L (U n is U {L + n}) */
#define BASE_LEVEL(c) ((c)->abs ? lv_const(0) : lv_hidden())

static void ctx_push(Ctx *c, const char *name, Val *ty, Val *val) {
    if (c->n == c->cap) {
        int cap = c->cap ? 2 * c->cap : 16;
        const char **nn = xalloc(cap * sizeof(char *)); Val **nt = xalloc(cap * sizeof(Val *));
        if (c->n) { memcpy(nn, c->names, c->n * sizeof(char *)); memcpy(nt, c->tys, c->n * sizeof(Val *)); }
        c->names = nn; c->tys = nt; c->cap = cap;
    }
    c->names[c->n] = name; c->tys[c->n] = ty; c->n++;
    c->env = env_push(c->env, val);
}
static void ctx_pop(Ctx *c) { c->n--; c->env = c->env->next; }
static void ctx_bind(Ctx *c, const char *name, Val *ty) { ctx_push(c, name, ty, ty->k == V_LEVEL ? vlvar(c->n) : vvar(c->n)); }
static void ctx_bind_i(Ctx *c, const char *name) { ctx_push(c, name, mkval(V_INTERVAL), vivar(c->n)); }
/* a fresh meta of a type, applied to the context: a level meta when the type is Level (solved by the level store) */
static Term *fresh_meta(Ctx *c, Val *ty, int line) {
    ty = force(ty);
    if (ty->k == V_LEVEL) { int m = lv_meta_new(); Term *t = mk_term(T_LMETA, NULL, NULL, NULL, NULL); t->n = m; return t; }
    return meta_term(meta_new(ty, c->n, c->names, line), c->n);
}

/* the context restricted to a face: types and environment values re-evaluated with the face's endpoints */
static Ctx ctx_restrict(Ctx *c, const Face *f) {
    Ctx r = {0}; r.n = c->n; r.cap = c->n;
    r.names = xalloc((c->n + 1) * sizeof(char *)); r.tys = xalloc((c->n + 1) * sizeof(Val *));
    Val **vs = xalloc((c->n + 1) * sizeof(Val *));
    for (int i = 0; i < c->n; i++) { r.names[i] = c->names[i]; r.tys[i] = restrict_val(c->tys[i], f); vs[c->n - 1 - i] = env_get(c->env, i); }
    for (int i = 0; i < c->n; i++) r.env = env_push(r.env, restrict_val(vs[i], f));
    return r;
}

static int cur_data = -1, cur_data_hi = -1;   /* the block of data types being declared, [cur_data, cur_data_hi): their occurrences are at the hidden level */
#define IN_DECL(d) ((d) >= cur_data && (d) < cur_data_hi)
static int find_def(const char *n) { for (int i = ndefs - 1; i >= 0; i--) if (!strcmp(defs[i].name, n)) return i; return -1; }
static int find_data(const char *n) { for (int i = ndatas - 1; i >= 0; i--) if (!strcmp(datas[i].name, n)) return i; return -1; }
static int find_con(const char *n) { for (int i = ncons - 1; i >= 0; i--) if (!strcmp(cons[i].name, n)) return i; return -1; }
static void check_fresh(const char *n, int line) {
    if (find_def(n) >= 0 || find_data(n) >= 0 || find_con(n) >= 0) die("line %d: '%s' is already defined", line, n);
}

static int term_binders(Term *t) {
    if (!t) return 0;
    int m = 0, x;
    x = term_binders(t->a); if (x > m) m = x;
    x = term_binders(t->b); if (x > m) m = x;
    x = term_binders(t->c); if (x > m) m = x;
    x = term_binders(t->d); if (x > m) m = x;
    for (int i = 0; i < t->nbr; i++) { x = term_binders(t->br[i].face); if (x > m) m = x; x = term_binders(t->br[i].body); if (x > m) m = x; }
    return m + (t->k == T_PI || t->k == T_LAM || t->k == T_LET);
}
static const char *show(Ctx *c, Val *v) {
    Term *t = quote(c->n, v);
    const char **names = xalloc((c->n + term_binders(t) + 1) * sizeof(char *));
    if (c->n) memcpy(names, c->names, c->n * sizeof(char *));
    char *buf = NULL; size_t sz = 0; FILE *f = open_memstream(&buf, &sz);
    term_print(f, t, names, c->n); fclose(f);
    char *s = xstrdup(buf); free(buf); return s;
}
static void expect_conv(Ctx *c, int line, Val *got, Val *want, const char *what) {
    if (!conv(c->n, got, want)) die("line %d: %s has type %s, expected %s", line, what, show(c, got), show(c, want));
}

int is_type_like(int depth, Val *ty) {
    switch (ty->k) {
    case V_U: case V_LEVEL: return 1;
    case V_PI: return is_type_like(depth + 1, inst(&ty->clo, ty->isi ? vivar(depth) : vvar(depth)));
    case V_PATHP: return is_type_like(depth + 1, vapp(ty->a, vivar(depth), 0));
    case V_PARTIAL: return is_type_like(depth, ty->b);
    case V_SUB: return is_type_like(depth, ty->a);
    case V_SIGMA: return is_type_like(depth, ty->dom) && is_type_like(depth + 1, inst(&ty->clo, vvar(depth)));
    case V_GLUE: return 0;
    default: return 0;
    }
}

static Term *infer(Ctx *c, STerm *s, Val **ty);
static Term *check(Ctx *c, STerm *s, Val *ty);

/* a term must be a type of either sort: returns its core, universe level and whether it is a pretype */
/* a type whose sort is not known yet (a meta, e.g. an implicit parameter still to be inferred) is in a universe at a fresh level */
static Val *refine_to_universe(Ctx *c, Val *ty) {
    ty = force(ty);
    if (ty->k == V_NEU && ty->h == H_META) { int l = lv_meta_new(); if (conv(c->n, ty, vu_l(lv_meta(l)))) ty = force(ty); }
    return ty;
}
static Term *check_type_sort(Ctx *c, STerm *s, LVal *lvl, int *pre) {
    Val *ty; Term *t = infer(c, s, &ty); ty = refine_to_universe(c, ty);
    if (ty->k != V_U) die("line %d: expected a type, but %s : %s", s->line, "the term", show(c, ty));
    *lvl = ty->lvl; *pre = ty->pre; return t;
}
/* a term must be a type in a universe (with Kan structure): pretypes are refused */
static Term *check_type(Ctx *c, STerm *s, LVal *lvl) {
    int pre; Term *t = check_type_sort(c, s, lvl, &pre);
    if (pre) die("line %d: a type in a universe is needed here, but the term is a pretype (Partial, Sub, Level, or a function from I) and has no Kan structure", s->line);
    return t;
}
/* a line of types  (i : I) -> U l : either a lambda over an interval variable, or a term whose type is such a function */
static Term *check_line(Ctx *c, STerm *s, LVal *lvl) {
    if (s->k == S_LAM) {
        ctx_bind_i(c, s->binders[0].name);
        Term *body = check_type(c, s->a, lvl);
        ctx_pop(c);
        Term *t = mk_lam(s->binders[0].name, body, 0); t->isi = 1; return t;
    }
    Val *ty; Term *t = infer(c, s, &ty); ty = force(ty);
    if (ty->k != V_PI || !ty->isi) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
    Val *cod = refine_to_universe(c, inst(&ty->clo, vivar(c->n)));
    if (cod->k != V_U) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
    if (cod->pre) die("line %d: expected a line of types (i : I) -> U, but the line yields pretypes: %s", s->line, show(c, ty));
    *lvl = cod->lvl; return t;
}
static Val *vinterval(void) { return mkval(V_INTERVAL); }
static Term *check_interval(Ctx *c, STerm *s) { return check(c, s, vinterval()); }

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
static Term *inst_tele(Term *t, int n, Term **vs, int k) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR:
        if (t->n < k) return t;
        if (t->n - k < n) return shift(vs[t->n - k], 0, k);
        return mk_var(t->n - n);
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return t;
    case T_PI:  r = mk_pi(t->name, inst_tele(t->a, n, vs, k), inst_tele(t->b, n, vs, k + 1), t->irr); r->isi = t->isi; r->pre = t->pre; return r;
    case T_LAM: r = mk_lam(t->name, inst_tele(t->a, n, vs, k + 1), t->irr); r->isi = t->isi; return r;
    case T_SIGMA: r = mk_term(T_SIGMA, inst_tele(t->a, n, vs, k), inst_tele(t->b, n, vs, k + 1), NULL, NULL); r->name = t->name; return r;
    case T_LET: return mk_let(t->name, inst_tele(t->a, n, vs, k), inst_tele(t->b, n, vs, k), inst_tele(t->c, n, vs, k + 1), t->irr);
    case T_SYS: {
        r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = inst_tele(t->br[i].face, n, vs, k); r->br[i].body = inst_tele(t->br[i].body, n, vs, k); }
        return r;
    }
    default:
        r = mk_term(t->k, inst_tele(t->a, n, vs, k), inst_tele(t->b, n, vs, k), inst_tele(t->c, n, vs, k), inst_tele(t->d, n, vs, k));
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; return r;
    }
}
static Term *E_con_spine(Term *t, EInfo *I, int depth) {
    /* t = c' p.. a'.. is.. (a constructor of the same data type applied): returns the method applied, or NULL */
    int nargs = 0; Term *w = t;
    while (w->k == T_APP) { nargs++; w = w->a; }
    if (w->k != T_CON || cons[w->n].data != I->C->data) return NULL;
    Con *Cp = con_at(w->n, I->dl); int np = I->np;
    if (Cp->bord >= I->o) die("the boundary of %s uses the later constructor %s; boundaries may only use earlier constructors", I->C->name, Cp->name);
    if (nargs != np + Cp->nargs + Cp->nint) die("internal: constructor %s applied to %d arguments in a boundary", Cp->name, nargs);
    Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
    for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    Term *m = mk_var(depth + I->n + I->htot + I->r + (I->o - 1 - Cp->bord));
    for (int j = 0; j < Cp->nargs; j++) m = mk_app(m, E(args[np + j], I, depth), Cp->args[j].irr);
    for (int j = 0; j < Cp->nargs; j++) if (Cp->args[j].isrec || Cp->args[j].isrecpath) {
        Term *ih = E(args[np + j], I, depth);
        if (ih == args[np + j] || term_eq(ih, args[np + j])) die("the boundary of %s: no induction hypothesis for the argument of %s", I->C->name, Cp->name);
        m = mk_app(m, ih, 0);
    }
    if (Cp->nint == 0) return m;
    /* a path constructor: its own boundary, instantiated along the spine ([params, args]: vs[0] is the last argument) */
    int tn = np + Cp->nargs; Term **vs = xalloc((tn + Cp->nint + 1) * sizeof(Term *));
    for (int j = 0; j < Cp->nargs; j++) vs[j] = args[np + Cp->nargs - 1 - j];
    for (int i = 0; i < np; i++) vs[Cp->nargs + i] = args[np - 1 - i];
    if (Cp->pathmethod) {   /* the method is a path: apply it, with the images of the boundary as endpoints */
        Term *x = E(inst_tele(boundary_at(Cp, 0), tn, vs, 0), I, depth);
        Term *y = E(inst_tele(boundary_at(Cp, 1), tn, vs, 0), I, depth);
        return mk_term(T_PAPP, m, args[np + Cp->nargs], x, y);
    }
    /* the method is a cube  (is : I) -> Sub (P idx (c p a is)) phi [faces -> E(boundary)]: apply it and take the element out */
    for (int q = 0; q < Cp->nint; q++) m = mk_app(m, args[np + Cp->nargs + q], 0);
    if (!Cp->boundary) return m;
    Term **vs2 = xalloc((tn + Cp->nint + 1) * sizeof(Term *));
    for (int q = 0; q < Cp->nint; q++) vs2[q] = args[np + Cp->nargs + Cp->nint - 1 - q];
    for (int i = 0; i < tn; i++) vs2[Cp->nint + i] = vs[i];
    Term *sys = E(inst_tele(Cp->boundary, tn + Cp->nint, vs2, 0), I, depth);
    Term *phi = NULL;
    for (int i = 0; i < sys->nbr; i++) phi = phi ? mk_term(T_IOR, phi, sys->br[i].face, NULL, NULL) : sys->br[i].face;
    Term *A = mk_var(depth + I->n + I->htot + I->r + I->o + (I->nb - 1 - I->pi));   /* P idx (c p a is) */
    Data *D = &datas[Cp->data];
    for (int j = 0; j < D->nidx; j++) A = mk_app(A, inst_tele(Cp->ridx[j], tn, vs, 0), 1);
    A = mk_app(A, t, 0);
    return mk_term(T_OUTS, A, phi ? phi : mk_term(T_I0, NULL, NULL, NULL, NULL), sys, m);
}
static Term *E(Term *t, EInfo *I, int depth) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR: {
        int idx = t->n - depth;
        if (idx >= I->n + I->htot && idx < I->n + I->htot + I->r) {
            int j = I->r - 1 - (idx - I->n - I->htot);
            if (I->record[j] >= 0) return mk_var(depth + I->n + (I->htot - 1 - I->record[j]));
        }
        return t;
    }
    case T_PAPP: {
        Term *h = E(t->a, I, depth);
        return mk_term(T_PAPP, h, t->b, E(t->c, I, depth), E(t->d, I, depth));
    }
    case T_APP: { Term *m = E_con_spine(t, I, depth); if (m) return m; return mk_app(E(t->a, I, depth), E(t->b, I, depth), t->irr); }
    case T_CON: { Term *m = E_con_spine(t, I, depth); if (m) return m; return t; }
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: case T_IAND: case T_IOR: case T_INEG: return t;
    case T_PI: r = mk_pi(t->name, E(t->a, I, depth), E(t->b, I, depth + 1), t->irr); r->isi = t->isi; return r;
    case T_LAM: r = mk_lam(t->name, E(t->a, I, depth + 1), t->irr); r->isi = t->isi; return r;
    case T_LET: return mk_let(t->name, E(t->a, I, depth), E(t->b, I, depth), E(t->c, I, depth + 1), t->irr);
    case T_SIGMA: r = mk_term(T_SIGMA, E(t->a, I, depth), E(t->b, I, depth + 1), NULL, NULL); r->name = t->name; return r;
    case T_SYS: {
        r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = t->br[i].face; r->br[i].body = E(t->br[i].body, I, depth); }
        return r;
    }
    default:
        r = mk_term(t->k, E(t->a, I, depth), E(t->b, I, depth), E(t->c, I, depth), E(t->d, I, depth));
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; return r;
    }
}
/* the boundary of C at an endpoint of its single interval: the body of the branch whose face holds there (under [params, args]) */
static Term *boundary_at(Con *C, int end) {
    Term *v = mk_term(end ? T_I1 : T_I0, NULL, NULL, NULL, NULL);
    for (int i = 0; i < C->boundary->nbr; i++) {
        Val *f = eval(NULL, subst_term(C->boundary->br[i].face, 0, v));
        if (iv_is_one(f->iv)) return subst_term(C->boundary->br[i].body, 0, v);
    }
    return NULL;
}
static Term *elim_type(int d, LVal lvl, int res_irr, LVal dl) {
    Data *D = data_at(d, dl); elim_dlt = mk_lval(dl);
    int np = D->nparams, m = D->nidx;
    /* the eliminators of a block share the prefix [params, P_0..P_{nbk-1}, methods of every member (K)] */
    int nbk = D->nblock, K = block_ncons(d), b0 = D->block, jpos = D->bpos;
    #define ITY(j) (D->itys[j])
    #define PTY(i) (D->ptys[i])
    #define ATY(C, j) ((C)->args[j].ty)
    /* body: P_j i x   under [params, P(nbk), mth(K), i(m), x] */
    Term *body = mk_var(1 + m + K + (nbk - 1 - jpos));
    for (int j = 0; j < m; j++) body = mk_app(body, mk_var(1 + (m - 1 - j)), 1);
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
        /* return: P_mi ridx (c p a is)   under [params, P(nbk), mth(o), a(r), ih(htot), iv(n)] */
        Term *ret = mk_var(n + htot + r + o + (nbk - 1 - mi));
        for (int j = 0; j < mm; j++) ret = mk_app(ret, shift2(C->ridx[j], n, htot, n + r, htot + o + nbk), 1);
        Term *ct = mk_ref_l(T_CON, M->cons[ci], elim_dlt);
        for (int i = 0; i < np; i++) ct = mk_app(ct, mk_var(n + htot + r + o + nbk + (np - 1 - i)), !C->bparams);
        for (int j = 0; j < r; j++) ct = mk_app(ct, mk_var(n + htot + (r - 1 - j)), C->args[j].irr);
        for (int q = 0; q < n; q++) ct = mk_app(ct, mk_var(n - 1 - q), 0);
        ret = mk_app(ret, ct, 0);
        Term *mt = ret;
        if (n > 0) {
            EInfo I = { C, n, r, htot, o, nbk, mi, np, dl, record };
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
        /* induction hypotheses, last first: an argument recursive in member rm gets its hypothesis from P_rm */
        int h = htot;
        for (int j = r - 1; j >= 0; j--) {
            ConArg *A = &C->args[j];
            int rm = (A->isrec || A->isrecpath) ? A->rec - b0 : 0;
            if (A->isrecpath) {   /* PathP (k. P_rm (a_j k)) E(px) E(py)   under [params, P, mth(o), a(r), ih(h)] */
                h--;
                EInfo Ih = { C, 0, r, h, o, nbk, mi, np, dl, record };
                Term *px = shift2(A->px, 0, h + (r - j), j, h + (r - j) + o + nbk), *py = shift2(A->py, 0, h + (r - j), j, h + (r - j) + o + nbk);
                Term *pa = mk_term(T_PAPP, mk_var((r - 1 - j) + h + 1), mk_var(0), shift(px, 0, 1), shift(py, 0, 1));
                Term *Pk = mk_var(1 + h + r + o + (nbk - 1 - rm));
                for (int q = 0; q < A->nidx; q++) Pk = mk_app(Pk, shift(shift2(A->idx[q], 0, h + (r - j), j, h + (r - j) + o + nbk), 0, 1), 1);
                Term *line = mk_lam("k", mk_app(Pk, pa, 0), 0); line->isi = 1;
                Term *ih = mk_term(T_PATHP, line, E(px, &Ih, 0), E(py, &Ih, 0), NULL);
                mt = mk_pi(xsprintf("ih%d", j), ih, mt, 0);
                continue;
            }
            if (!A->isrec) continue;
            h--;
            int q = A->npi;
            /* P_rm idx[y] (a_j y..)   under [params, P, mth(o), a(r), ih(h), y(q)] */
            Term *ih = mk_var(q + h + r + o + (nbk - 1 - rm));
            for (int i = 0; i < A->nidx; i++) ih = mk_app(ih, shift2(A->idx[i], q, h + (r - j), q + j, h + (r - j) + o + nbk), 1);
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
    /* motives, the last member's first: P_i : (idx_i..) -> D_i p idx -> U lvl   under [params, P_0..P_{i-1}] */
    for (int mi = nbk - 1; mi >= 0; mi--) {
        Data *M = data_at(b0 + mi, dl); int mm = M->nidx; int rel = M->hit || M->nidx > 0;   /* relevant with the motive: hcomp is a formal element */
        Term *P = mk_pi("x", data_applied(b0 + mi, mm + mi, 0), mk_u_l(lvl), 0);
        for (int j = mm - 1; j >= 0; j--) P = mk_pi(xsprintf("i%d", j), shift(M->itys[j], j, mi), P, !rel);
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
typedef struct { STerm *num; Val *dom; int meta; } Deferred;   /* a numeral argument whose type is not known yet: a meta stands for it */
static Deferred *dnums; static int ndnums;
static Term *check_numeral(Ctx *c, STerm *s, Val *ty);
/* the deferred numerals whose types are known now are checked and their metas assigned; all: the rest are errors */
static void resolve_numerals(Ctx *c, int all) {
    int j = 0;
    for (int i = 0; i < ndnums; i++) {
        Val *dom = force(dnums[i].dom);
        if (dom->k == V_NEU && dom->h == H_META) {
            if (all) die("line %d: the type of the numeral %llu is not determined; write the implicit argument, f {e} ..", dnums[i].num->line, dnums[i].num->num);
            dnums[j++] = dnums[i]; continue;
        }
        meta_assign(dnums[i].meta, check_numeral(c, dnums[i].num, dom), tmetas[dnums[i].meta].ctxn);
    }
    ndnums = j;
}
static Term *app_spine(Ctx *c, STerm **args, int nargs, Term *head, Val *hty, Val **ty) {
    for (int i = 0; i < nargs; i++) {
        hty = force(hty);
        while (hty->k == V_PI && hty->imp && !args[i]->imp) {   /* an implicit argument not written: a meta */
            Term *m = fresh_meta(c, hty->dom, args[i]->line);
            head = mk_app(head, m, hty->irr); hty = force(inst(&hty->clo, eval(c->env, m)));
        }
        if (hty->k == V_PI && args[i]->k == S_NUM) {   /* a numeral against a type not known yet: checked after the other arguments */
            Val *dom = force(hty->dom);
            if (dom->k == V_NEU && dom->h == H_META) {
                int id = meta_new(dom, c->n, c->names, args[i]->line); Term *m = meta_term(id, c->n); tmetas[id].deferred = 1;
                dnums = realloc(dnums, (ndnums + 1) * sizeof(Deferred)); if (!dnums) die("out of memory");
                dnums[ndnums].num = args[i]; dnums[ndnums].dom = dom; dnums[ndnums].meta = id; ndnums++;
                head = mk_app(head, m, hty->irr); hty = inst(&hty->clo, eval(c->env, m));
                continue;
            }
        }
        if (hty->k == V_PATHP) {
            Term *r = check_interval(c, args[i]);
            head = mk_term(T_PAPP, head, r, quote(c->n, hty->b), quote(c->n, hty->c));
            hty = vapp(hty->a, eval(c->env, r), 0);
            continue;
        }
        if (hty->k != V_PI) die("line %d: applying a non-function of type %s", args[i]->line, show(c, hty));
        Term *a = check(c, args[i], hty->dom);
        head = mk_app(head, a, hty->irr);
        hty = inst(&hty->clo, eval(c->env, a));
    }
    *ty = hty; return head;
}

static void need_args(STerm *h, int n, int want, const char *what) {
    if (n < want) die("line %d: %s needs %d argument%s", h->line, what, want, want == 1 ? "" : "s");
}
/* the faces of phi as a list; dies if phi is not an interval value */
static int faces_of(Val *phi, Face **fs) { if (phi->k != V_I) die("internal: face expected"); return iv_faces(phi->iv, fs); }

static Term *infer_app(Ctx *c, STerm *s, Val **ty) {
    STerm **args = NULL; int n = 0, cap = 0;
    STerm *h = s;
    while (h->k == S_APP) {
        if (n == cap) { cap = cap ? 2 * cap : 8; STerm **na = xalloc(cap * sizeof(STerm *)); if (n) memcpy(na, args, n * sizeof(STerm *)); args = na; }
        args[n++] = h->b; h = h->a;
    }
    for (int i = 0; i < n / 2; i++) { STerm *t = args[i]; args[i] = args[n - 1 - i]; args[n - 1 - i] = t; }
    switch (h->k) {
    case S_ELIM: {
        int d = find_data(h->name);
        if (d >= 0 && IN_DECL(d))   /* its constructors are not all declared yet: an eliminator here would have too few methods */
            die("line %d: elim %s inside the declaration of %s: the type is not complete yet", s->line, h->name, h->name);
        if (d < 0) die("line %d: elim of unknown data type '%s'", h->line, h->name);
        Data *D = &datas[d]; int np = D->nparams;
        /* the data type is taken at a fresh level (a meta, solved at the end of the definition), or at its
           own hidden level inside its own declaration */
        LVal dl; Term *dlt = global_level(T_DATA, d, &dl);
        Data *DV = data_at(d, dl);
        Env *pe = NULL; Val **pv = xalloc((np + 1) * sizeof(Val *)); Term **pt = xalloc((np + 1) * sizeof(Term *)); int ai = 0;
        for (int i = 0; i < np; i++) {   /* the parameters are implicit: written {p}, or metas */
            Val *pty = eval(pe, DV->ptys[i]);
            pt[i] = (ai < n && args[ai]->imp) ? check(c, args[ai++], pty) : fresh_meta(c, pty, h->line);
            pv[i] = eval(c->env, pt[i]); pe = env_push(pe, pv[i]);
        }
        if (n < ai + 1) die("line %d: elim %s needs a motive", h->line, D->name);
        /* motive: peel its lambdas against the expected binders (indices, then the target),
           then read the universe of what remains */
        LVal lvl; int res_irr;
        {
            STerm *ms = args[ai]; Env *ie = pe; int nb = 0, depth = c->n;
            int d0 = D->block, m0 = datas[d0].nidx; Data *DV0 = data_at(d0, dl);   /* the first motive is the block's first member's */
            Val **iv = xalloc((m0 + 2) * sizeof(Val *));
            #define TARGET_TYPE(dst) do { \
                Val *dv_ = mkval(V_DATA); dv_->n = d0; dv_->lvl = dl; \
                for (int i_ = 0; i_ < np; i_++) { vl_push(&dv_->args, pv[i_], 1); } \
                for (int j_ = 0; j_ < m0; j_++) { vl_push(&dv_->args, iv[j_], 1); } \
                (dst) = dv_; } while (0)
            while (nb <= m0 && ms->k == S_LAM) {
                Val *dom;
                if (nb < m0) dom = eval(ie, DV0->itys[nb]); else TARGET_TYPE(dom);
                ctx_bind(c, ms->binders[0].name, dom);
                Val *x = vvar(c->n - 1); depth = c->n;
                if (nb < m0) { iv[nb] = x; ie = env_push(ie, x); }
                ms = ms->a; nb++;
            }
            Val *rty; Term *rt = infer(c, ms, &rty);
            Val *cur = rty;
            for (int j = nb; j <= m0; j++) {
                if (cur->k != V_PI) die("line %d: motive for %s must abstract over %d index%s and the target", ms->line, datas[d0].name, m0, m0 == 1 ? "" : "es");
                Val *dom;
                if (j < m0) dom = eval(ie, DV0->itys[j]); else TARGET_TYPE(dom);
                expect_conv(c, ms->line, cur->dom, dom, "motive binder");
                Val *x = vvar(depth++);
                if (j < m0) { iv[j] = x; ie = env_push(ie, x); }
                cur = inst(&cur->clo, x);
            }
            #undef TARGET_TYPE
            if (cur->k != V_U || cur->pre) die("line %d: motive for %s must land in a universe, not %s", ms->line, datas[d0].name, show(c, cur));
            lvl = cur->lvl;
            Val *fib = eval(c->env, rt);
            for (int j = nb; j <= m0; j++) fib = vapp(fib, vvar(c->n + (j - nb)), 0);
            (void)fib; res_irr = 0;
            for (int i = 0; i < nb; i++) ctx_pop(c);
        }
        Term *ety = elim_type(d, lvl, res_irr, dl);
        Term *head = mk_ref_l(T_ELIM, d, dlt); Val *hty = eval(NULL, ety);
        for (int i = 0; i < np; i++) { head = mk_app(head, pt[i], 1); hty = inst(&hty->clo, pv[i]); }
        return app_spine(c, args + ai, n - ai, head, hty, ty);
    }
    case S_PATHP: {
        LVal lvl; Term *line, *x, *y;
        if (h->lvl == 0) {   /* PathP line x y */
            need_args(h, n, 3, "PathP");
            line = check_line(c, args[0], &lvl);
        } else {             /* Path A x y = PathP (\_ -> A) x y */
            need_args(h, n, 3, "Path");
            Term *A = check_type(c, args[0], &lvl);
            line = mk_lam("_", shift(A, 0, 1), 0); line->isi = 1;
        }
        Val *lv = eval(c->env, line);
        x = check(c, args[1], vapp(lv, vi(iv_zero()), 0));
        y = check(c, args[2], vapp(lv, vi(iv_one()), 0));
        return app_spine(c, args + 3, n - 3, mk_term(T_PATHP, line, x, y, NULL), vu_l(lvl), ty);
    }
    case S_PARTIAL: {
        need_args(h, n, 2, "Partial");
        Term *phi = check_interval(c, args[0]);
        LVal lvl; Term *A = check_type(c, args[1], &lvl);
        return app_spine(c, args + 2, n - 2, mk_term(T_PARTIAL, phi, A, NULL, NULL), vupre_l(lvl), ty);
    }
    case S_TRANSP: {
        need_args(h, n, 3, "transp");
        LVal lvl; Term *line = check_line(c, args[0], &lvl);
        Val *lv = eval(c->env, line);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        Term *u0 = check(c, args[2], vapp(lv, vi(iv_zero()), 0));
        /* the line must be constant wherever phi holds */
        Val *Ai = vapp(lv, vivar(c->n), 0), *A0 = vapp(lv, vi(iv_zero()), 0);
        Face *fs; int nf = faces_of(pv, &fs);
        for (int i = 0; i < nf; i++)
            if (!conv(c->n + 1, restrict_val(Ai, &fs[i]), restrict_val(A0, &fs[i])))
                die("line %d: transp: the line %s is not constant on the face where it must be the identity", args[0]->line, show(c, lv));
        Term *t = mk_term(T_TRANSP, line, phi, u0, NULL);
        t->n = !val_mentions_ivar(c->n + 1, Ai, c->n);     /* a constant line: erasure may drop the transport */
        return app_spine(c, args + 3, n - 3, t, vapp(lv, vi(iv_one()), 0), ty);
    }
    case S_HCOMP: {
        need_args(h, n, 4, "hcomp");
        LVal lvl; Term *A = check_type(c, args[0], &lvl); Val *Av = eval(c->env, A);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        /* u : (i : I) -> Partial phi A */
        Val *uty = mkval(V_PI); uty->name = "i"; uty->isi = 1; uty->dom = vinterval();
        uty->clo.env = c->env; uty->clo.t = mk_term(T_PARTIAL, shift(phi, 0, 1), shift(A, 0, 1), NULL, NULL);
        Term *u = check(c, args[2], uty); Val *uv = eval(c->env, u);
        Term *u0 = check(c, args[3], Av); Val *u0v = eval(c->env, u0);
        /* the base must agree with the sides at i0 wherever phi holds */
        Face *fs; int nf = faces_of(pv, &fs);
        for (int i = 0; i < nf; i++) {
            Val *side = vsys_at(vapp(uv, vi(iv_zero()), 0), &fs[i]);
            if (!side) die("line %d: hcomp: the sides do not cover their face", args[2]->line);
            if (!conv(c->n, side, restrict_val(u0v, &fs[i])))
                die("line %d: hcomp: the base does not agree with the sides at i0 on a face of %s", args[3]->line, show(c, pv));
        }
        Term *t = mk_term(T_HCOMP, A, phi, u, u0); t->n = (Av->k == V_U);
        return app_spine(c, args + 4, n - 4, t, Av, ty);
    }
    case S_COMP: {
        /* comp A phi u u0 : A i1  with  u : (i : I) -> Partial phi (A i),  u0 : A i0 agreeing with u i0 on phi.
           Elaborated to its definition in terms of hcomp and transp (Cohen-Huber-Mortberg):
             hcomp (A i1) phi (\i -> [ phi -> transp (\j -> A (i \/ j)) i (u i) ]) (transp A i0 u0)   */
        need_args(h, n, 4, "comp");
        LVal lvl; Term *line = check_line(c, args[0], &lvl); Val *lv = eval(c->env, line);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        Val *uty = mkval(V_PI); uty->name = "i"; uty->isi = 1; uty->dom = vinterval();
        uty->clo.env = c->env; uty->clo.t = mk_term(T_PARTIAL, shift(phi, 0, 1), mk_app(shift(line, 0, 1), mk_var(0), 0), NULL, NULL);
        Term *u = check(c, args[2], uty); Val *uv = eval(c->env, u);
        Term *u0 = check(c, args[3], vapp(lv, vi(iv_zero()), 0)); Val *u0v = eval(c->env, u0);
        Face *fs; int nf = faces_of(pv, &fs);
        for (int i = 0; i < nf; i++) {
            Val *side = vsys_at(vapp(uv, vi(iv_zero()), 0), &fs[i]);
            if (!side) die("line %d: comp: the sides do not cover their face", args[2]->line);
            if (!conv(c->n, side, restrict_val(u0v, &fs[i])))
                die("line %d: comp: the base does not agree with the sides at i0 on a face of %s", args[3]->line, show(c, pv));
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
        return app_spine(c, args + 4, n - 4, t, vapp(lv, vi(iv_one()), 0), ty);
    }
    case S_SUB: {   /* Sub A phi u : U,  u : Partial phi A */
        need_args(h, n, 3, "Sub");
        LVal lvl; Term *A = check_type(c, args[0], &lvl); Val *Av = eval(c->env, A);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        Val *pty = mkval(V_PARTIAL); pty->a = pv; pty->b = Av;
        Term *u = check(c, args[2], pty);
        return app_spine(c, args + 3, n - 3, mk_term(T_SUB, A, phi, u, NULL), vupre_l(lvl), ty);
    }
    case S_SIGMA: {  /* Sigma A B : U,  B : A -> U (a lambda, or a term of that type) */
        need_args(h, n, 2, "Sigma");
        LVal la, lb; Term *A = check_type(c, args[0], &la); Val *Av = eval(c->env, A);
        Term *B;
        if (args[1]->k == S_LAM) {
            ctx_bind(c, args[1]->binders[0].name, Av);
            Term *body = check_type(c, args[1]->a, &lb);
            ctx_pop(c);
            B = body;
            Term *t = mk_term(T_SIGMA, A, B, NULL, NULL); t->name = args[1]->binders[0].name;
            return app_spine(c, args + 2, n - 2, t, vu_l(lv_max(la, lb)), ty);
        }
        Val *bty; Term *bt = infer(c, args[1], &bty);
        if (bty->k != V_PI) die("line %d: the second argument of Sigma must be a family A -> U", args[1]->line);
        expect_conv(c, args[1]->line, bty->dom, Av, "family domain");
        Val *cod = inst(&bty->clo, vvar(c->n));
        if (cod->k != V_U || cod->pre) die("line %d: the second argument of Sigma must be a family A -> U", args[1]->line);
        lb = cod->lvl;
        Term *t = mk_term(T_SIGMA, A, mk_app(shift(bt, 0, 1), mk_var(0), 0), NULL, NULL); t->name = "x";
        return app_spine(c, args + 2, n - 2, t, vu_l(lv_max(la, lb)), ty);
    }
    case S_FST: case S_SND: {
        need_args(h, n, 1, h->k == S_FST ? "fst" : "snd");
        Val *pty; Term *p = infer(c, args[0], &pty);
        if (pty->k != V_SIGMA) die("line %d: projection from a term of type %s, expected a Sigma type", args[0]->line, show(c, pty));
        Term *t = mk_term(h->k == S_FST ? T_FST : T_SND, p, NULL, NULL, NULL);
        Val *rty = h->k == S_FST ? pty->dom : inst(&pty->clo, vproj(eval(c->env, p), 1));
        return app_spine(c, args + 1, n - 1, t, rty, ty);
    }
    case S_GLUE: {   /* Glue A phi Te : U,  Te : Partial phi (Sigma U (\T -> Equiv T A)) */
        need_args(h, n, 3, "Glue");
        LVal lvl; Term *A = check_type(c, args[0], &lvl); Val *Av = eval(c->env, A);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        int eq = find_def("Equiv"); if (eq < 0) die("line %d: Glue needs the definition 'Equiv' (in the prelude)", h->line);
        Val *sig = mkval(V_SIGMA); sig->name = "T"; sig->dom = vu_l(lvl);
        sig->clo.env = env_push(c->env, Av);   /* under [.., A]: Equiv^lvl T A with T the bound variable */
        sig->clo.t = mk_app(mk_app(mk_ref_l(T_DEF, eq, mk_lval(lvl)), mk_var(0), 0), mk_var(1), 0);
        Val *pty = mkval(V_PARTIAL); pty->a = pv; pty->b = sig;
        Term *Te = check(c, args[2], pty);
        Term *g = mk_term(T_GLUE, A, phi, Te, mk_lval(lvl));   /* the level, for the rules' equivProof */
        return app_spine(c, args + 3, n - 3, g, vu_l(lvl), ty);
    }
    case S_GLUEEL: die("line %d: glue must be checked against a Glue type", h->line);
    case S_UNGLUE: {
        need_args(h, n, 1, "unglue");
        Val *bty; Term *b = infer(c, args[0], &bty);
        if (bty->k != V_GLUE) die("line %d: unglue applied to a term of type %s, expected a Glue type", args[0]->line, show(c, bty));
        Term *t = mk_term(T_UNGLUE, b, quote(c->n, bty->a), quote(c->n, bty->b), quote(c->n, bty->c));
        return app_spine(c, args + 1, n - 1, t, bty->a, ty);
    }
    case S_INS: die("line %d: inS must be checked against a Sub type", h->line);
    case S_OUTS: {  /* outS s : A  for s : Sub A phi u */
        need_args(h, n, 1, "outS");
        Val *sty; Term *s = infer(c, args[0], &sty);
        if (sty->k != V_SUB) die("line %d: outS applied to a term of type %s, expected a Sub type", args[0]->line, show(c, sty));
        Term *t = mk_term(T_OUTS, quote(c->n, sty->a), quote(c->n, sty->b), quote(c->n, sty->c), s);
        return app_spine(c, args + 1, n - 1, t, sty->a, ty);
    }
    default: {
        Val *hty; Term *head = infer(c, h, &hty);
        return app_spine(c, args, n, head, hty, ty);
    }
    }
}

/* ---- systems ---- */

typedef Val *(*TypeAt)(const Face *f, void *data);
static Val *partial_type_at(const Face *f, void *data) { return restrict_val((Val *)data, f); }
static Val *glue_type_at(const Face *f, void *data) {   /* the glued type T on a face: fst of the (T, e) there */
    Val *Te = vsys_at((Val *)data, f);
    if (!Te) die("internal: glue: no glued type on this face");
    return vproj(Te, 1);
}
static Term *check_system_at(Ctx *c, STerm *s, Val *phi, TypeAt tyat, void *data);
static Term *check_system(Ctx *c, STerm *s, Val *ty) {
    if (ty->k != V_PARTIAL) die("line %d: a system must be checked against a Partial type, not %s", s->line, show(c, ty));
    return check_system_at(c, s, ty->a, partial_type_at, ty->b);
}
static Term *check_system_at(Ctx *c, STerm *s, Val *phi, TypeAt tyat, void *data) {
    Term *t = mk_term(T_SYS, NULL, NULL, NULL, NULL); t->nbr = s->nbr; t->br = xalloc((s->nbr + 1) * sizeof(TBranch));
    Val **psi = xalloc((s->nbr + 1) * sizeof(Val *)), **bv = xalloc((s->nbr + 1) * sizeof(Val *));
    IVal cover = iv_zero();
    for (int k = 0; k < s->nbr; k++) {
        t->br[k].face = check_interval(c, s->br[k].face);
        psi[k] = eval(c->env, t->br[k].face);
        cover = iv_or(cover, psi[k]->iv);
    }
    if (!iv_eq(cover, phi->iv)) die("line %d: the system's faces cover %s, but its type demands %s", s->line, show(c, vi(cover)), show(c, phi));
    for (int k = 0; k < s->nbr; k++) {
        Face *fs; int nf = faces_of(psi[k], &fs);
        if (nf == 0) die("line %d: the face %s of a system branch is never satisfied", s->br[k].face->line, show(c, psi[k]));
        Term *body = NULL;
        for (int i = 0; i < nf; i++) {
            Ctx rc = ctx_restrict(c, &fs[i]);
            Term *b = check(&rc, s->br[k].body, tyat(&fs[i], data));
            if (!body) body = b;
        }
        t->br[k].body = body;
    }
    (void)bv;
    /* overlapping branches must agree: both evaluated under the restriction to the common face */
    for (int k = 0; k < s->nbr; k++) for (int l = k + 1; l < s->nbr; l++) {
        Face *fs; int nf = faces_of(vi(iv_and(psi[k]->iv, psi[l]->iv)), &fs);
        for (int i = 0; i < nf; i++) {
            Ctx rc = ctx_restrict(c, &fs[i]);
            if (!conv(c->n, eval(rc.env, t->br[k].body), eval(rc.env, t->br[l].body)))
                die("line %d: system branches %d and %d disagree where their faces overlap", s->line, k + 1, l + 1);
        }
    }
    return t;
}

/* ---- terms ---- */

static Term *infer(Ctx *c, STerm *s, Val **ty) {
    switch (s->k) {
    case S_VAR: {
        for (int i = c->n - 1; i >= 0; i--)
            if (!strcmp(c->names[i], s->name)) { *ty = c->tys[i]; return mk_var(c->n - 1 - i); }
        int id;
        if ((id = find_con(s->name)) >= 0) { LVal L; Term *lt = global_level(T_CON, id, &L); *ty = eval(NULL, con_at(id, L)->ty); return mk_ref_l(T_CON, id, lt); }
        if ((id = find_def(s->name)) >= 0) { LVal L; Term *lt = global_level(T_DEF, id, &L); *ty = def_ty_at(id, L); return mk_ref_l(T_DEF, id, lt); }
        if ((id = find_data(s->name)) >= 0) { LVal L; Term *lt = global_level(T_DATA, id, &L); *ty = eval(NULL, data_at(id, L)->ty); return mk_ref_l(T_DATA, id, lt); }
        die("line %d: unbound name '%s'", s->line, s->name);
    }
    case S_HOLE: {   /* a hole standing for a type: a meta in a universe at a fresh level */
        int l = lv_meta_new(); Val *U = vu_l(lv_meta(l)); *ty = U; return fresh_meta(c, U, s->line);
    }
    case S_U:
        if (s->a) {   /* U {l}: a universe at a level expression */
            Term *lt = check(c, s->a, vlevel()); LVal L = eval_level(c->env, lt);
            Term *u = mk_u(0); u->a = lt; *ty = vu_l(lv_add(L, 1)); return u;
        }
        *ty = vu_l(lv_add(BASE_LEVEL(c), s->lvl + 1)); return mk_u_l(lv_add(BASE_LEVEL(c), s->lvl));   /* U n is U {L + n}, or U n when level-explicit */
    case S_LEVEL: *ty = vupre(0); return mk_term(T_LEVEL, NULL, NULL, NULL, NULL);   /* a pretype: no Kan structure, not inductive */
    case S_LZERO: *ty = vlevel(); return mk_lval(BASE_LEVEL(c));   /* constants are relative to the hidden level unless level-explicit */
    case S_LSUC: { Term *a = check(c, s->a, vlevel()); Term *r = mk_term(T_LSUC, a, NULL, NULL, NULL); r->n = 1; *ty = vlevel(); return r; }
    case S_LMAX: { Term *a = check(c, s->a, vlevel()), *b = check(c, s->b, vlevel()); *ty = vlevel(); return mk_term(T_LMAX, a, b, NULL, NULL); }
    case S_I: die("line %d: I is the type of interval variables; it is not itself a term of a universe", s->line);
    case S_I0: *ty = vinterval(); return mk_term(T_I0, NULL, NULL, NULL, NULL);
    case S_I1: *ty = vinterval(); return mk_term(T_I1, NULL, NULL, NULL, NULL);
    case S_IAND: case S_IOR: {
        Term *a = check_interval(c, s->a), *b = check_interval(c, s->b);
        *ty = vinterval(); return mk_term(s->k == S_IAND ? T_IAND : T_IOR, a, b, NULL, NULL);
    }
    case S_INEG: { Term *a = check_interval(c, s->a); *ty = vinterval(); return mk_term(T_INEG, a, NULL, NULL, NULL); }
    case S_NUM:
        die("line %d: the type of the numeral %llu is not determined here; a numeral is checked against a type shaped like the naturals (give it one: a binder, a let, an argument)", s->line, s->num);
    case S_PI: {
        SBinder *b = &s->binders[0];
        if (b->ty->k == S_I) {   /* a function from the interval is a pretype: it has no Kan structure */
            if (b->imp) die("line %d: an interval binder cannot be implicit", s->line);
            ctx_bind_i(c, b->name);
            LVal lb; int pb; Term *cod = check_type_sort(c, s->a, &lb, &pb);
            ctx_pop(c);
            *ty = vupre_l(lb);
            Term *t = mk_pi(b->name, mk_term(T_INTERVAL, NULL, NULL, NULL, NULL), cod, 0); return t;
        }
        LVal la, lb; int pa, pb; Term *dom = check_type_sort(c, b->ty, &la, &pa);
        Val *dv = eval(c->env, dom);
        int irr = dom->k == T_LEVEL;   /* types are run-time codes, so every binder is relevant; levels are not */
        ctx_bind(c, b->name, dv);
        Term *cod = check_type_sort(c, s->a, &lb, &pb);
        ctx_pop(c);
        LVal l = lv_max(la, lb);
        *ty = (pa || pb) ? vupre_l(l) : vu_l(l);   /* a function type from or into a pretype is a pretype */
        Term *t = mk_pi(b->name, dom, cod, irr); t->pre = pa; t->imp = b->imp; return t;
    }
    case S_LAM: die("line %d: cannot infer the type of a lambda; add an annotation", s->line);
    case S_SYS: die("line %d: cannot infer the type of a system; it must be checked against a Partial type", s->line);
    case S_PAIR: die("line %d: cannot infer the type of a pair; it must be checked against a Sigma type", s->line);
    case S_APP: case S_ELIM: case S_PATHP: case S_PARTIAL: case S_TRANSP: case S_HCOMP: case S_COMP: case S_SUB: case S_INS: case S_OUTS: case S_SIGMA: case S_FST: case S_SND: case S_GLUE: case S_GLUEEL: case S_UNGLUE: return infer_app(c, s, ty);
    case S_LET: {
        LVal l; int p; Term *tyt = check_type_sort(c, s->a, &l, &p);   /* a let may bind a line or a partial element */
        Val *tv = eval(c->env, tyt);
        Term *v = check(c, s->b, tv);
        int irr = 0;
        ctx_push(c, s->name, tv, eval(c->env, v));
        Val *bty; Term *body = infer(c, s->c, &bty);
        ctx_pop(c);
        *ty = bty;
        return mk_let(s->name, tyt, v, body, irr);
    }
    }
    return NULL;
}

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
static Term *check_numeral(Ctx *c, STerm *s, Val *ty) {
    int zi, si;
    if (ty->k == V_LEVEL) {   /* a numeral is also a constant level */
        if (s->num > 1000000) die("line %d: the level %llu is too large", s->line, s->num);
        return mk_lval(lv_add(BASE_LEVEL(c), (int)s->num));
    }
    if (ty->k != V_DATA || ty->args.n != 0 || !peano_shape(ty->n, &zi, &si))
        die("line %d: the numeral %llu needs a type shaped like the naturals (a nullary constructor and one with a single recursive argument), not %s", s->line, s->num, show(c, ty));
    Term *zero = mk_ref_l(T_CON, zi, mk_lval(ty->lvl)), *suc = mk_ref_l(T_CON, si, mk_lval(ty->lvl)), *D = mk_ref_l(T_DATA, ty->n, mk_lval(ty->lvl));
    unsigned long long n = s->num;
    if (n == 0) return zero;
    if (n == 1) return mk_app(suc, zero, 0);
    int K = 0; for (unsigned long long m = n; m; m >>= 1) K++;
    Term *body = zero;
    for (int i = 0; i < K; i++) if (n >> i & 1) body = mk_app(mk_var(K - 1 - i), body, 0);
    for (int i = K - 1; i >= 0; i--) {
        char *name = xalloc(32); snprintf(name, 32, "s%llu", 1ULL << i);
        Term *val = i == 0 ? suc : mk_lam("x", mk_app(mk_var(1), mk_app(mk_var(1), mk_var(0), 0), 0), 0);
        body = mk_let(name, mk_pi("_", D, D, 0), val, body, 0);
    }
    return body;
}
static Term *check(Ctx *c, STerm *s, Val *ty) {
    ty = force(ty);
    if (ty->k == V_PI && ty->imp && !(s->k == S_LAM && s->binders[0].imp)) {   /* an implicit function type: abstract over the argument */
        const char *nm = xsprintf("{%s}", ty->name ? ty->name : "_");   /* not a name the program can write: no capture */
        ctx_bind(c, nm, ty->dom);
        Term *body = check(c, s, inst(&ty->clo, c->env->v));
        ctx_pop(c);
        Term *t = mk_lam(nm, body, ty->irr); t->imp = 1; return t;
    }
    if (s->k == S_HOLE) return fresh_meta(c, ty, s->line);
    if (s->k == S_NUM) return check_numeral(c, s, ty);
    if (s->k == S_LAM) {
        SBinder *b = &s->binders[0];
        if (b->imp && !(ty->k == V_PI && ty->imp)) die("line %d: the implicit lambda \\{%s} is checked against %s, not an implicit function type", s->line, b->name, show(c, ty));
        if (ty->k == V_PATHP) {
            ctx_bind_i(c, b->name);
            int lvl = c->n - 1;
            Term *body = check(c, s->a, vapp(ty->a, vivar(lvl), 0));
            Val *bv = eval(c->env, body);
            int var = lvl, v0 = 0, v1 = 1; Face f0 = { &var, &v0, 1 }, f1 = { &var, &v1, 1 };
            if (!conv(c->n, restrict_val(bv, &f0), ty->b)) die("line %d: the path's left endpoint is %s, expected %s", s->line, show(c, restrict_val(bv, &f0)), show(c, ty->b));
            if (!conv(c->n, restrict_val(bv, &f1), ty->c)) die("line %d: the path's right endpoint is %s, expected %s", s->line, show(c, restrict_val(bv, &f1)), show(c, ty->c));
            ctx_pop(c);
            Term *t = mk_lam(b->name, body, 0); t->isi = 1; return t;
        }
        if (ty->k != V_PI) die("line %d: lambda checked against non-function type %s", s->line, show(c, ty));
        if (ty->isi) {
            ctx_bind_i(c, b->name);
            Term *body = check(c, s->a, inst(&ty->clo, vivar(c->n - 1)));
            ctx_pop(c);
            Term *t = mk_lam(b->name, body, 0); t->isi = 1; return t;
        }
        ctx_bind(c, b->name, ty->dom);
        Term *body = check(c, s->a, inst(&ty->clo, vvar(c->n - 1)));
        ctx_pop(c);
        Term *t = mk_lam(b->name, body, ty->irr); t->imp = b->imp; return t;
    }
    if (s->k == S_LET) {
        LVal l; int p; Term *tyt = check_type_sort(c, s->a, &l, &p);
        Val *tv = eval(c->env, tyt);
        Term *v = check(c, s->b, tv);
        int irr = 0;
        ctx_push(c, s->name, tv, eval(c->env, v));
        Term *body = check(c, s->c, ty);
        ctx_pop(c);
        return mk_let(s->name, tyt, v, body, irr);
    }
    if (s->k == S_APP && s->a->k == S_INS) {   /* inS x : Sub A phi u  when x : A agrees with u on phi */
        if (ty->k != V_SUB) die("line %d: inS checked against %s, expected a Sub type", s->line, show(c, ty));
        Term *x = check(c, s->b, ty->a); Val *xv = eval(c->env, x);
        Face *fs; int nf = faces_of(ty->b, &fs);
        for (int i = 0; i < nf; i++) {
            Val *side = vsys_at(ty->c, &fs[i]);
            if (!side || !conv(c->n, restrict_val(xv, &fs[i]), side))
                die("line %d: inS: the element does not agree with the subtype's sides on a face of %s", s->line, show(c, ty->b));
        }
        return mk_term(T_INS, x, NULL, NULL, NULL);
    }
    if (s->k == S_APP && s->a->k == S_APP && s->a->a->k == S_GLUEEL) {   /* glue ts a : Glue A phi Te */
        if (ty->k != V_GLUE) die("line %d: glue checked against %s, expected a Glue type", s->line, show(c, ty));
        STerm *tss = s->a->b, *as = s->b;
        if (tss->k != S_SYS) die("line %d: the first argument of glue must be a system", tss->line);
        Term *tst = check_system_at(c, tss, ty->b, glue_type_at, ty->c);
        Val *tsv = eval(c->env, tst);
        Term *a = check(c, as, ty->a); Val *av = eval(c->env, a);
        Face *fs; int nf = faces_of(ty->b, &fs);
        for (int i = 0; i < nf; i++) {
            Val *Te = vsys_at(ty->c, &fs[i]), *t = vsys_at(tsv, &fs[i]);
            if (!Te || !t) die("line %d: glue: the sides do not cover their face", s->line);
            Val *ea = vapp(vproj(vproj(Te, 2), 1), t, 0);
            if (!conv(c->n, restrict_val(av, &fs[i]), ea))
                die("line %d: glue: the base does not agree with the equivalence applied to the sides on a face of %s", s->line, show(c, ty->b));
        }
        return mk_term(T_GLUEEL, tst, a, quote(c->n, ty), NULL);
    }
    if (s->k == S_PAIR) {
        if (ty->k != V_SIGMA) die("line %d: pair checked against %s, expected a Sigma type", s->line, show(c, ty));
        Term *a = check(c, s->a, ty->dom);
        Term *b = check(c, s->b, inst(&ty->clo, eval(c->env, a)));
        return mk_term(T_PAIR, a, b, NULL, NULL);
    }
    if (s->k == S_SYS) return check_system(c, s, ty);
    Val *got; Term *t = infer(c, s, &got); got = force(got);
    while (got->k == V_PI && got->imp) {   /* trailing implicit arguments are supplied */
        Term *m = fresh_meta(c, got->dom, s->line);
        t = mk_app(t, m, got->irr); got = force(inst(&got->clo, eval(c->env, m)));
    }
    if (got->k == V_U && ty->k == V_NEU && ty->h == H_META) {
        /* a universe against a type not known yet: subtyping holds between sorts only, so the type is a universe of the same
           sort at a level to be determined; the level is a fresh level meta, bounded below by got's (the level store decides it) */
        Val *U = vu_l(lv_meta(lv_meta_new())); U->pre = got->pre;
        if (!conv(c->n, ty, U)) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
        if (lv_enforce_leq(got->lvl, U->lvl) != 1) die("line %d: universe inconsistency: %s is not below %s", s->line, show(c, got), show(c, U));
        resolve_numerals(c, 0); return t;
    }
    if (got->k == V_U && ty->k == V_U && got->pre <= ty->pre) {   /* cumulativity (a universe type is also a pretype): enforce got <= expected */
        int r = lv_enforce_leq(got->lvl, ty->lvl);
        if (r == 1) { resolve_numerals(c, 0); return t; }
        if (r < 0) die("line %d: level ambiguous: whether %s is below %s cannot be decided; write the level, f {l} ..", s->line, show(c, got), show(c, ty));
        die("line %d: universe inconsistency: %s is not below %s", s->line, show(c, got), show(c, ty));
    }
    if (got->k == V_PARTIAL && ty->k != V_PARTIAL && iv_is_one(got->a->iv)) got = got->b;   /* a partial element on a face that holds is an element */
    if (!conv(c->n, got, ty)) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
    resolve_numerals(c, 0);
    return t;
}

/* ---- declarations ---- */

/* does the declared type (binder sugar folded into a Pi chain) bind a Level? */
static int declares_level(STerm *t) {
    for (; t && t->k == S_PI; t = t->a) if (t->binders[0].ty && t->binders[0].ty->k == S_LEVEL) return 1;
    return 0;
}

/* does the term mention the hidden level, other than as the level of an occurrence of a member of the block [lo, hi)? */
static int mentions_hidden_but_block(Term *t, int lo, int hi) {
    if (!t) return 0;
    switch (t->k) {
    case T_LVAL: return lv_mentions_hidden(t->lvl);
    case T_DATA: case T_ELIM: return (t->n >= lo && t->n < hi) ? 0 : mentions_hidden_but_block(t->a, lo, hi);
    case T_CON: return (cons[t->n].data >= lo && cons[t->n].data < hi) ? 0 : mentions_hidden_but_block(t->a, lo, hi);
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (mentions_hidden_but_block(t->br[i].face, lo, hi) || mentions_hidden_but_block(t->br[i].body, lo, hi)) return 1; return 0;
    default: return mentions_hidden_but_block(t->a, lo, hi) || mentions_hidden_but_block(t->b, lo, hi) || mentions_hidden_but_block(t->c, lo, hi) || mentions_hidden_but_block(t->d, lo, hi);
    }
}
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
static int mentions_range(Term *t, int lo, int hi) {
    if (!t) return 0;
    switch (t->k) {
    case T_DATA: return t->n >= lo && t->n < hi;
    case T_VAR: case T_U: case T_DEF: case T_CON: case T_ELIM: case T_INTERVAL: case T_I0: case T_I1: return 0;
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (mentions_range(t->br[i].face, lo, hi) || mentions_range(t->br[i].body, lo, hi)) return 1; return 0;
    default: return mentions_range(t->a, lo, hi) || mentions_range(t->b, lo, hi) || mentions_range(t->c, lo, hi) || mentions_range(t->d, lo, hi);
    }
}
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
static int mentions_essentially(Term *t, int idx) {
    if (!t) return 0;
    switch (t->k) {
    case T_VAR: return t->n == idx;
    case T_APP: {
        int nargs = 0; Term *w = t;
        while (w->k == T_APP) { nargs++; w = w->a; }
        if (w->k == T_CON) {
            int np = datas[cons[w->n].data].nparams;
            Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
            for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
            for (int i = np; i < nargs; i++) if (mentions_essentially(args[i], idx)) return 1;
            return 0;
        }
        return mentions_essentially(t->a, idx) || mentions_essentially(t->b, idx);
    }
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return 0;
    case T_PI: case T_SIGMA: return mentions_essentially(t->a, idx) || mentions_essentially(t->b, idx + 1);
    case T_LAM: return mentions_essentially(t->a, idx + 1);
    case T_LET: return mentions_essentially(t->a, idx) || mentions_essentially(t->b, idx) || mentions_essentially(t->c, idx + 1);
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (mentions_essentially(t->br[i].face, idx) || mentions_essentially(t->br[i].body, idx)) return 1; return 0;
    default: return mentions_essentially(t->a, idx) || mentions_essentially(t->b, idx) || mentions_essentially(t->c, idx) || mentions_essentially(t->d, idx);
    }
}
/* The boundary grammar (CHM18, 3.2): an element of D in a boundary is a recursive argument of the constructor, a
   recursive path argument applied to an interval, a recursive argument of function type applied, or an earlier
   constructor of D applied to the parameters, to arguments by this grammar and to intervals. Nothing else stands for
   an element of D (no Kan operation, eliminator, definition or let), and no recursive argument appears at a position
   whose type is not D: the eliminator images recursive arguments by their induction hypotheses, which inhabit the
   motive, so a recursive argument at any other position would give the method an ill-typed boundary.
   Context of a boundary: [params(np), args(r), intervals(nint)] (+ depth under binders opened inside it). */
typedef struct { Con *C; int np, r, nint, line; } BGram;
static const char *bg_D(BGram *g) { return datas[g->C->data].name; }
/* a variable standing for a recursive argument of the constructor: its ordinal in *j */
static int bg_rec_var(BGram *g, Term *t, int depth, int *j) {
    if (t->k != T_VAR || t->n < depth) return 0;
    int idx = t->n - depth;
    if (idx < g->nint || idx >= g->nint + g->r) return 0;
    *j = g->r - 1 - (idx - g->nint);
    return g->C->args[*j].isrec || g->C->args[*j].isrecpath;
}
/* a position whose type is not D: no recursive argument inside */
static void bg_no_rec(BGram *g, Term *t, int depth) {
    if (!t) return;
    int j;
    if (bg_rec_var(g, t, depth, &j))
        die("line %d: the boundary of %s uses the recursive argument %s at a position whose type is not %s; a recursive argument may only stand for an element of %s (its image under the eliminator is an induction hypothesis)",
            g->line, g->C->name, g->C->args[j].name, bg_D(g), bg_D(g));
    switch (t->k) {
    case T_PI: case T_SIGMA: bg_no_rec(g, t->a, depth); bg_no_rec(g, t->b, depth + 1); return;
    case T_LAM: bg_no_rec(g, t->a, depth + 1); return;
    case T_LET: bg_no_rec(g, t->a, depth); bg_no_rec(g, t->b, depth); bg_no_rec(g, t->c, depth + 1); return;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { bg_no_rec(g, t->br[i].face, depth); bg_no_rec(g, t->br[i].body, depth); } return;
    default: bg_no_rec(g, t->a, depth); bg_no_rec(g, t->b, depth); bg_no_rec(g, t->c, depth); bg_no_rec(g, t->d, depth); return;
    }
}
static void bg_elem(BGram *g, Term *t, int depth);
/* a path in D: a recursive path argument, or an abstraction over an interval whose body is an element */
static void bg_path(BGram *g, Term *t, int depth) {
    int j;
    if (bg_rec_var(g, t, depth, &j) && g->C->args[j].isrecpath) return;
    if (t->k == T_LAM && t->isi) { bg_elem(g, t->a, depth + 1); return; }
    die("line %d: the boundary of %s: a path in %s must be a recursive path argument or an abstraction over an interval", g->line, g->C->name, bg_D(g));
}
/* an element of D */
static void bg_elem(BGram *g, Term *t, int depth) {
    int j;
    if (bg_rec_var(g, t, depth, &j)) {
        if (g->C->args[j].isrec && g->C->args[j].npi == 0) return;
        die("line %d: the boundary of %s: the recursive argument %s is not an element of %s; apply it", g->line, g->C->name, g->C->args[j].name, bg_D(g));
    }
    if (t->k == T_PAPP) {   /* a recursive path argument at an interval */
        if (bg_rec_var(g, t->a, depth, &j) && g->C->args[j].isrecpath) { bg_no_rec(g, t->b, depth); return; }
        die("line %d: the boundary of %s: only a recursive path argument may be applied to an interval here", g->line, g->C->name);
    }
    int nargs = 0; Term *w = t;
    while (w->k == T_APP) { nargs++; w = w->a; }
    if (bg_rec_var(g, w, depth, &j)) {   /* a recursive argument of function type, applied */
        if (!g->C->args[j].isrec || nargs != g->C->args[j].npi)
            die("line %d: the boundary of %s: the recursive argument %s must be applied to exactly its %d argument%s", g->line, g->C->name, g->C->args[j].name, g->C->args[j].npi, g->C->args[j].npi == 1 ? "" : "s");
        for (Term *x = t; x->k == T_APP; x = x->a) bg_no_rec(g, x->b, depth);
        return;
    }
    if (w->k != T_CON || cons[w->n].data != g->C->data)
        die("line %d: the boundary of %s: an element of %s in a boundary must be a recursive argument or an earlier constructor applied; a Kan operation, eliminator, definition or let cannot stand for one (CHM18 3.2)",
            g->line, g->C->name, bg_D(g));
    Con *Cp = &cons[w->n];
    if (Cp->ci >= g->C->ci) die("line %d: the boundary of %s uses the later constructor %s; boundaries may only use earlier constructors", g->line, g->C->name, Cp->name);
    if (nargs != g->np + Cp->nargs + Cp->nint)
        die("line %d: the boundary of %s applies %s to %d arguments, expected %d", g->line, g->C->name, Cp->name, nargs, g->np + Cp->nargs + Cp->nint);
    Term **args = xalloc((nargs + 1) * sizeof(Term *)); w = t;
    for (int i = nargs - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    for (int i = 0; i < g->np; i++) bg_no_rec(g, args[i], depth);
    for (int q = 0; q < Cp->nargs; q++) {
        Term *a = args[g->np + q]; ConArg *A = &Cp->args[q];
        if (A->isrecpath) bg_path(g, a, depth);
        else if (!A->isrec) bg_no_rec(g, a, depth);
        else if (A->npi == 0) bg_elem(g, a, depth);
        else {   /* a function into D: an abstraction over its arguments whose body is an element */
            Term *b = a; int k = 0;
            while (k < A->npi && b->k == T_LAM && !b->isi) { b = b->a; k++; }
            if (k < A->npi) die("line %d: the boundary of %s: the argument %s of %s (a function into %s) must be an abstraction", g->line, g->C->name, A->name, Cp->name, bg_D(g));
            bg_elem(g, b, depth + k);
        }
    }
    for (int q = 0; q < Cp->nint; q++) bg_no_rec(g, args[g->np + Cp->nargs + q], depth);
}

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
    datas = realloc(datas, (ndatas + n) * sizeof(Data)); if (!datas) die("out of memory");
    for (int i = 0; i < n; i++) {
        SDecl *s = ms[i];
        Data D = {0}; D.name = s->name; D.line = s->line; D.nparams = nparams; D.ptys = ptys;
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
                BGram g = { &C, nparams, r, nint, sc->line };
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
        cons = realloc(cons, (ncons + 1) * sizeof(Con)); if (!cons) die("out of memory");
        cons[ncons++] = C;
        Data *DD = &datas[d];
        DD->cons = realloc(DD->cons, (DD->ncons + 1) * sizeof(int)); if (!DD->cons) die("out of memory");
        DD->cons[DD->ncons++] = cid;
      }
    }
    cur_data = -1; cur_data_hi = -1;
    /* every term of the block, for solving the metas and deciding polymorphism */
    int nt = 0, cap = 64; Term **ts = xalloc(cap * sizeof(Term *)); Term ***slots = xalloc(cap * sizeof(Term **)); int *isty = xalloc(cap * sizeof(int));
    #define SLOT(p) do { if (nt == cap) { cap *= 2; ts = realloc(ts, cap * sizeof(Term *)); slots = realloc(slots, cap * sizeof(Term **)); isty = realloc(isty, cap * sizeof(int)); if (!ts || !slots || !isty) die("out of memory"); } slots[nt] = &(p); isty[nt] = 0; ts[nt++] = (p); } while (0)
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
    resolve_numerals(&c, 0); metas_finish(ms[0]->name, line, mm0); resolve_numerals(&c, 1);
    for (int i = 0; i < nt; i++) ts[i] = zonk(ts[i]);
    LVal *lvs = xalloc((n + 1) * sizeof(LVal)); for (int i = 0; i < n; i++) lvs[i] = datas[d0 + i].lvl;
    solve_metas(ms[0]->name, line, m0, mark, ts, nt, lvs, n);
    for (int i = 0; i < nt; i++) *slots[i] = ts[i];
    for (int i = 0; i < n; i++) datas[d0 + i].lvl = lvs[i];
    /* polymorphic if some parameter, index or constructor mentions the hidden level (the members' own universes do not
       count, nor do the levels of their own occurrences, which are at the hidden level by construction) */
    int poly = 0;
    for (int i = 0; i < nt; i++) if (!isty[i] && mentions_hidden_but_block(ts[i], d0, d0 + n)) poly = 1;
    if (!poly) {   /* not polymorphic: the hidden level is 0 */
        for (int i = 0; i < nt; i++) *slots[i] = subst_hidden(ts[i], lv_const(0));
        for (int i = 0; i < n; i++) datas[d0 + i].lvl = lv_subst(datas[d0 + i].lvl, -1, lv_const(0));
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
    Term *val = check(&c, s->val, vty);
    resolve_numerals(&c, 0); metas_finish(s->name, s->line, mm0); resolve_numerals(&c, 1);
    Term *ts[2] = { zonk(ty), zonk(val) };
    solve_metas(s->name, s->line, m0, mark, ts, 2, NULL, 0);
    ty = ts[0]; val = ts[1];
    Def D = {0}; D.name = s->name; D.line = s->line;
    D.poly = term_mentions_hidden(ty) || term_mentions_hidden(val);
    if (!D.poly) { ty = subst_hidden(ty, lv_const(0)); val = subst_hidden(val, lv_const(0)); }
    D.ty = ty; D.val = val;
    D.vty = eval(NULL, D.poly ? subst_hidden(ty, lv_const(0)) : ty);
    D.vval = eval(NULL, D.poly ? subst_hidden(val, lv_const(0)) : val);
    D.irr = is_type_like(0, D.vty);
    defs = realloc(defs, (ndefs + 1) * sizeof(Def)); if (!defs) die("out of memory");
    defs[ndefs++] = D;
}

void elab_program(SDecl *decls) {
    for (SDecl *s = decls; s; s = s->next) {
        if (s->isdata == 2) elab_block(s->members, s->nmembers, s->params, s->nparams, s->line);
        else if (s->isdata) elab_data(s); else elab_def(s);
    }
}
