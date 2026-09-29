/*
 * eval.c - core terms, interval algebra, values, normalization by
 * evaluation, restriction to faces, and the Kan operations.
 *
 * Terms use de Bruijn indices; values use de Bruijn levels for free
 * variables.  Interval values are elements of the free De Morgan algebra
 * on the interval variables in irredundant disjunctive normal form (which
 * is canonical: the free De Morgan algebra on X is the free distributive
 * lattice on X and its formal reversals).  A face is a partial assignment
 * of interval variables to endpoints; restricting a value to a face
 * re-evaluates it with the assignment, so that stuck path applications and
 * Kan operations get another chance to compute.
 *
 * Computation rules beyond beta: iota for eliminators; endpoints of path
 * application; transp and hcomp on functions, paths, universes and
 * inductive types, following Cohen-Coquand-Huber-Mortberg and the Cubical
 * Agda reducer (see Programs/Reference/agda).
 */
#include "tt.h"

Def *defs; int ndefs; Data *datas; int ndatas; Con *cons; int ncons;
static LVal elim_lvl;   /* the level of the eliminator being reduced (set by vapp) */

/* ---- memory / errors ---- */
void unfold_counts_report(void); void fallback_report(void);
/* the resource abort is the memory layer's (libeezo/mem.h); these diagnostics run first (main registers them) */
void resource_diagnostics(void) { unfold_counts_report(); fallback_report(); }

/* A memo entry stays valid across metas generations iff nothing inside it was blocked on an unsolved meta: resolving one
   can resume a reduction the entry took as neutral. A missed entry is merely slow, so this is set conservatively -
   every place that hands back a neutral where a decision was possible marks it, meta or not. */
static int meta_blocked;
/* The checker's values, terms, environments ... live for the run: one arena of the memory layer (libeezo/mem.h),
   zeroed; its budget is the layer's (EEZOTT_MAX_ALLOC, set in main - the harness's cap, not the theory's) */
static Arena tt_arena;
void *xalloc(size_t n) { return arena_alloc(&tt_arena, n); }
char *xstrdup(const char *s) { size_t n = strlen(s) + 1; char *p = xalloc(n); memcpy(p, s, n); return p; }
char *xsprintf(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt); int n = vsnprintf(NULL, 0, fmt, ap); va_end(ap);
    char *s = xalloc(n + 1); va_start(ap, fmt); vsnprintf(s, n + 1, fmt, ap); va_end(ap); return s;
}
void die(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt); fprintf(stderr, "eezott: "); vfprintf(stderr, fmt, ap); fputc('\n', stderr); va_end(ap);
    exit(1);
}

/* ---- terms ---- */
static Term *mk(TKind k) { Term *t = xalloc(sizeof *t); t->k = k; return t; }
Term *mk_var(int i) { Term *t = mk(T_VAR); t->n = i; return t; }
Term *mk_u(int l) { Term *t = mk(T_U); t->n = l; return t; }
Term *mk_upre(int l) { Term *t = mk_u(l); t->pre = 1; return t; }
Term *mk_pi(const char *x, Term *a, Term *b, int irr) { Term *t = mk(T_PI); t->name = x; t->a = a; t->b = b; t->irr = irr; t->isi = (a->k == T_INTERVAL); return t; }
Term *mk_lam(const char *x, Term *body, int irr) { Term *t = mk(T_LAM); t->name = x; t->a = body; t->irr = irr; return t; }
Term *mk_app(Term *f, Term *a, int irr) { Term *t = mk(T_APP); t->a = f; t->b = a; t->irr = irr; return t; }
Term *mk_let(const char *x, Term *ty, Term *v, Term *body, int irr) { Term *t = mk(T_LET); t->name = x; t->a = ty; t->b = v; t->c = body; t->irr = irr; return t; }
Term *mk_ref(TKind k, int id) { Term *t = mk(k); t->n = id; return t; }
/* does the global take a level? */
int ref_poly(TKind k, int id) {
    switch (k) { case T_DEF: return defs[id].poly; case T_DATA: case T_ELIM: return datas[id].poly; case T_CON: return datas[cons[id].data].poly; default: return 1; }
}
Term *mk_ref_l(TKind k, int id, Term *lt) { Term *t = mk(k); t->n = id; t->a = ref_poly(k, id) ? lt : NULL; return t; }
Term *mk_lval(LVal l) { Term *t = mk(T_LVAL); t->lvl = l; return t; }
Term *mk_u_l(LVal l) { Term *u = mk_u(0); u->a = mk_lval(l); return u; }

/* a generic map over a term's level values (embedded levels, and nothing else carries them) */
static Term *map_levels(Term *t, LVal (*f)(LVal, void *), void *data) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_LVAL: return mk_lval(f(t->lvl, data));
    case T_LMETA: return mk_lval(f(lv_meta(t->n), data));   /* a meta as a term becomes an embedded value */
    case T_VAR: case T_LEVEL: case T_LZERO: case T_INTERVAL: case T_I0: case T_I1: return t;
    case T_SYS: {
        r = mk_term(T_SYS, NULL, NULL, NULL, NULL); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = map_levels(t->br[i].face, f, data); r->br[i].body = map_levels(t->br[i].body, f, data); }
        return r;
    }
    default:
        r = mk_term(t->k, map_levels(t->a, f, data), map_levels(t->b, f, data), map_levels(t->c, f, data), map_levels(t->d, f, data));
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->pre = t->pre; r->lvl = t->lvl; r->imp = t->imp; r->num = t->num; return r;
    }
}
static LVal f_hidden(LVal l, void *data) { return lv_subst(l, -1, *(LVal *)data); }
Term *subst_hidden(Term *t, LVal L) { return map_levels(t, f_hidden, &L); }
typedef struct { LVal *sol; int m0; } MetaSubst;
static LVal f_metas(LVal l, void *data) {
    MetaSubst *ms = data;
    for (int i = 0; i < l.n; i++) if (l.t[i].meta && l.t[i].var >= ms->m0) { int id = l.t[i].var; l = lv_subst_meta(l, id, ms->sol[id - ms->m0]); i = -1; }
    return l;
}
Term *subst_metas(Term *t, LVal *sol, int m0) {
    MetaSubst ms = { sol, m0 };
    /* metas also occur as terms (T_LMETA) in level expressions: replace those first */
    Term *r = map_levels(t, f_metas, &ms);
    return r;
}
int term_mentions_hidden(Term *t) {
    if (!t) return 0;
    switch (t->k) {
    case T_LVAL: return lv_mentions_hidden(t->lvl);
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (term_mentions_hidden(t->br[i].face) || term_mentions_hidden(t->br[i].body)) return 1; return 0;
    default: return term_mentions_hidden(t->a) || term_mentions_hidden(t->b) || term_mentions_hidden(t->c) || term_mentions_hidden(t->d);
    }
}

/* ---- globals taken at a level ---- */
typedef struct { LVal l; void *inst; } LMemo;
typedef struct { LMemo *m; int n, cap; } LMemoList;
static void *lmemo_get(LMemoList *ml, LVal L) { for (int i = 0; i < ml->n; i++) if (lv_eq(ml->m[i].l, L)) return ml->m[i].inst; return NULL; }
static void lmemo_put(LMemoList *ml, LVal L, void *inst) {
    if (ml->n == ml->cap) { ml->cap = ml->cap ? 2 * ml->cap : 8; LMemo *nm = xalloc(ml->cap * sizeof(LMemo)); for (int i = 0; i < ml->n; i++) nm[i] = ml->m[i]; ml->m = nm; }
    ml->m[ml->n].l = L; ml->m[ml->n].inst = inst; ml->n++;
}
static LMemoList *con_memo, *data_memo; static int ncon_memo, ndata_memo;
static LMemoList *memo_for(LMemoList **arr, int *n, int id) {
    if (id >= *n) { int m = id + 16; LMemoList *na = xalloc(m * sizeof(LMemoList)); for (int i = 0; i < *n; i++) na[i] = (*arr)[i]; *arr = na; *n = m; }
    return &(*arr)[id];
}
/* def_at is the machine's (below) */
Val *def_ty_at(int id, LVal L) {
    Def *d = &defs[id]; int n;
    if (!d->poly) return d->vty;
    if (!lv_is_const(L, &n)) {
        static LMemoList *tm; static int ntm;
        LMemoList *ml = memo_for(&tm, &ntm, id); Val *r = lmemo_get(ml, L);
        if (!r) { r = eval(NULL, subst_hidden(d->ty, L)); lmemo_put(ml, L, r); }
        return r;
    }
    def_at(id, L);
    if (!d->vty_at[n]) d->vty_at[n] = eval(NULL, subst_hidden(d->ty, L));
    return d->vty_at[n];
}
static Con *con_instance(Con *C, LVal L) {
    Con *r = xalloc(sizeof *r); *r = *C;
    r->ty = subst_hidden(C->ty, L);
    r->args = xalloc((C->nargs + 1) * sizeof(ConArg));
    for (int j = 0; j < C->nargs; j++) {
        ConArg *A = &r->args[j]; *A = C->args[j];
        A->ty = subst_hidden(A->ty, L);
        if (A->nidx) { A->idx = xalloc((A->nidx + 1) * sizeof(Term *)); for (int q = 0; q < A->nidx; q++) A->idx[q] = subst_hidden(C->args[j].idx[q], L); }
        A->px = subst_hidden(A->px, L); A->py = subst_hidden(A->py, L);
    }
    Data *D = &datas[C->data];
    if (D->nidx) { r->ridx = xalloc((D->nidx + 1) * sizeof(Term *)); for (int j = 0; j < D->nidx; j++) r->ridx[j] = subst_hidden(C->ridx[j], L); }
    r->boundary = subst_hidden(C->boundary, L);
    r->at = NULL; r->nat = 0;
    return r;
}
Con *con_at(int ci, LVal L) {
    Con *C = &cons[ci]; int n;
    if (!datas[C->data].poly) return C;
    if (!lv_is_const(L, &n)) {
        LMemoList *ml = memo_for(&con_memo, &ncon_memo, ci); Con *r = lmemo_get(ml, L);
        if (!r) { r = con_instance(C, L); lmemo_put(ml, L, r); }
        return r;
    }
    if (n >= C->nat) { int m = n + 4; Con **na = xalloc(m * sizeof(Con *)); for (int i = 0; i < C->nat; i++) na[i] = C->at[i]; C->at = na; C->nat = m; }
    if (!C->at[n]) C->at[n] = con_instance(C, L);
    return C->at[n];
}
static Data *data_instance(Data *D, LVal L) {
    Data *r = xalloc(sizeof *r); *r = *D;
    r->ptys = xalloc((D->nparams + 1) * sizeof(Term *)); for (int i = 0; i < D->nparams; i++) r->ptys[i] = subst_hidden(D->ptys[i], L);
    r->itys = xalloc((D->nidx + 1) * sizeof(Term *)); for (int j = 0; j < D->nidx; j++) r->itys[j] = subst_hidden(D->itys[j], L);
    r->ty = subst_hidden(D->ty, L); r->lvl = lv_subst(D->lvl, -1, L);
    r->at = NULL; r->nat = 0;
    return r;
}
Data *data_at(int d, LVal L) {
    Data *D = &datas[d]; int n;
    if (!D->poly) return D;
    if (!lv_is_const(L, &n)) {
        LMemoList *ml = memo_for(&data_memo, &ndata_memo, d); Data *r = lmemo_get(ml, L);
        if (!r) { r = data_instance(D, L); lmemo_put(ml, L, r); }
        return r;
    }
    if (n >= D->nat) { int m = n + 4; Data **na = xalloc(m * sizeof(Data *)); for (int i = 0; i < D->nat; i++) na[i] = D->at[i]; D->at = na; D->nat = m; }
    if (!D->at[n]) D->at[n] = data_instance(D, L);
    return D->at[n];
}
int block_ncons(int d) { Data *D = &datas[d]; int K = 0; for (int i = 0; i < D->nblock; i++) K += datas[D->block + i].ncons; return K; }
/* the eliminators of a block share a prefix [params, P_0..P_{nb-1}, methods(K)]: is its i-th entry computationally irrelevant? */
static int prefix_irr(int d, int i) { Data *D = &datas[d]; if (i < D->nparams) return 1; i -= D->nparams; if (i < D->nblock) { Data *M = &datas[D->block + i]; return !(M->hit || M->nidx > 0); } return 0; }
Term *mk_term(TKind k, Term *a, Term *b, Term *c, Term *d) { Term *t = mk(k); t->a = a; t->b = b; t->c = c; t->d = d; return t; }

Term *shift2(Term *t, int cut1, int by1, int cut2, int by2) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR:
        if (t->n >= cut2) return mk_var(t->n + by2);
        if (t->n >= cut1) return mk_var(t->n + by1);
        return t;
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return t;
    case T_PI:  r = mk_pi(t->name, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1 + 1, by1, cut2 + 1, by2), t->irr); r->isi = t->isi; r->imp = t->imp; return r;
    case T_LAM: r = mk_lam(t->name, shift2(t->a, cut1 + 1, by1, cut2 + 1, by2), t->irr); r->isi = t->isi; r->imp = t->imp; return r;
    case T_SIGMA: r = mk_term(T_SIGMA, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1 + 1, by1, cut2 + 1, by2), NULL, NULL); r->name = t->name; return r;
    case T_APP: return mk_app(shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1, by1, cut2, by2), t->irr);
    case T_LET: return mk_let(t->name, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1, by1, cut2, by2),
                              shift2(t->c, cut1 + 1, by1, cut2 + 1, by2), t->irr);
    case T_SYS: {
        r = mk(T_SYS); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = shift2(t->br[i].face, cut1, by1, cut2, by2); r->br[i].body = shift2(t->br[i].body, cut1, by1, cut2, by2); }
        return r;
    }
    default:
        r = mk_term(t->k, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1, by1, cut2, by2),
                    shift2(t->c, cut1, by1, cut2, by2), shift2(t->d, cut1, by1, cut2, by2));
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->lvl = t->lvl; r->pre = t->pre; r->imp = t->imp; r->num = t->num; return r;
    }
}
Term *shift(Term *t, int cut, int by) { return shift2(t, cut, by, cut, by); }
Term *subst_term(Term *t, int idx, Term *v) {       /* v closed */
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR: if (t->n == idx) return v; if (t->n > idx) return mk_var(t->n - 1); return t;
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return t;
    case T_PI:  r = mk_pi(t->name, subst_term(t->a, idx, v), subst_term(t->b, idx + 1, v), t->irr); r->isi = t->isi; r->imp = t->imp; return r;
    case T_LAM: r = mk_lam(t->name, subst_term(t->a, idx + 1, v), t->irr); r->isi = t->isi; r->imp = t->imp; return r;
    case T_SIGMA: r = mk_term(T_SIGMA, subst_term(t->a, idx, v), subst_term(t->b, idx + 1, v), NULL, NULL); r->name = t->name; return r;
    case T_LET: return mk_let(t->name, subst_term(t->a, idx, v), subst_term(t->b, idx, v), subst_term(t->c, idx + 1, v), t->irr);
    case T_SYS: {
        r = mk(T_SYS); r->nbr = t->nbr; r->br = xalloc((t->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < t->nbr; i++) { r->br[i].face = subst_term(t->br[i].face, idx, v); r->br[i].body = subst_term(t->br[i].body, idx, v); }
        return r;
    }
    default:
        r = mk_term(t->k, subst_term(t->a, idx, v), subst_term(t->b, idx, v), subst_term(t->c, idx, v), subst_term(t->d, idx, v));
        r->n = t->n; r->irr = t->irr; r->name = t->name; r->isi = t->isi; r->lvl = t->lvl; r->pre = t->pre; r->imp = t->imp; r->num = t->num; return r;
    }
}

int term_eq(Term *a, Term *b) {
    if (a == b) return 1;
    if (!a || !b || a->k != b->k) return 0;
    switch (a->k) {
    case T_VAR: return a->n == b->n;
    case T_U: return a->n == b->n && a->pre == b->pre && term_eq(a->a, b->a);
    case T_LEVEL: return 1;
    case T_LZERO: case T_LMETA: case T_META: return a->n == b->n;
    case T_LSUC: return a->n == b->n && term_eq(a->a, b->a);
    case T_DEF: case T_DATA: case T_CON: case T_ELIM: return a->n == b->n && term_eq(a->a, b->a);
    case T_NUM: return a->n == b->n && term_eq(a->a, b->a) && bn_cmp(a->num, b->num) == 0;
    case T_LVAL: return lv_eq(a->lvl, b->lvl);
    case T_INTERVAL: case T_I0: case T_I1: return 1;
    case T_SYS:
        if (a->nbr != b->nbr) return 0;
        for (int i = 0; i < a->nbr; i++) if (!term_eq(a->br[i].face, b->br[i].face) || !term_eq(a->br[i].body, b->br[i].body)) return 0;
        return 1;
    default: return term_eq(a->a, b->a) && term_eq(a->b, b->b) && term_eq(a->c, b->c) && term_eq(a->d, b->d);
    }
}
int term_mentions_var(Term *t, int idx) {
    if (!t) return 0;
    switch (t->k) {
    case T_VAR: return t->n == idx;
    case T_LEVEL: case T_LZERO: case T_LMETA: case T_LVAL: case T_INTERVAL: case T_I0: case T_I1: return 0;
    case T_PI: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx + 1);
    case T_LAM: return term_mentions_var(t->a, idx + 1);
    case T_SIGMA: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx + 1);
    case T_LET: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx) || term_mentions_var(t->c, idx + 1);
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (term_mentions_var(t->br[i].face, idx) || term_mentions_var(t->br[i].body, idx)) return 1; return 0;
    default: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx) || term_mentions_var(t->c, idx) || term_mentions_var(t->d, idx);
    }
}

/* printing with names: names[] indexed by de Bruijn level, depth = number bound */
/* a closed constructor spine of a type shaped like the naturals: suc (suc (... zero)); returns 1 and its value */
static int numeral_of(Term *t, unsigned long long *out) {
    unsigned long long n = 0; int zi, si, d = -1;
    while (t->k == T_APP && t->a->k == T_CON) {
        if (d < 0) { d = cons[t->a->n].data; if (!peano_shape(d, &zi, &si)) return 0; }
        if (t->a->n != si) return 0;
        n++; t = t->b;
    }
    if (t->k != T_CON) return 0;
    if (d < 0) { d = cons[t->n].data; if (!peano_shape(d, &zi, &si)) return 0; }
    if (t->n != zi) return 0;
    *out = n; return 1;
}
/* a level value: the hidden level reads as its offset alone (U n, f^n), others as lmax of lsuc^n applied to names */
static void lv_tp(FILE *f, LVal l, const char **names, int depth, int prec) {
    int hn;
    if (lv_is_hidden_plus(l, &hn)) { fprintf(f, "%d", hn); return; }
    int ns = l.n + (l.c > 0 || l.n == 0 ? 1 : 0);
    if (ns > 1 && prec > 0) fputc('(', f);
    for (int i = 0; i < l.n; i++) {
        if (i + 1 < ns) fputs("lmax ", f);
        for (int q = 0; q < l.t[i].off; q++) fputs("lsuc (", f);
        if (l.t[i].meta) fprintf(f, "?%d", l.t[i].var);
        else if (l.t[i].var == -1) fputs("L", f);
        else { int lv = l.t[i].var; if (lv >= 0 && lv < depth && names[lv]) fprintf(f, "%s", names[lv]); else fprintf(f, "#l%d", lv); }
        for (int q = 0; q < l.t[i].off; q++) fputc(')', f);
        if (i + 1 < ns) fputc(' ', f);
    }
    if (l.c > 0 || l.n == 0) fprintf(f, "%d", l.c);
    if (ns > 1 && prec > 0) fputc(')', f);
}
/* ---- printing ----
   An explicit machine, not C recursion: the pieces still to print - terms, strings, binder names to bring into scope -
   sit on a heap stack in output order, and the binder names in scope live in a table that grows with the depth (the
   caller's names seed it), so a term prints however deep it is. */
typedef enum { PT_TERM, PT_STR, PT_NAME } PKind;
typedef struct { PKind k; Term *t; int depth, prec; const char *s; } PItem;
static Stack pst = { NULL, 0, 0, sizeof(PItem) };   /* a Stack of the memory layer (libeezo/mem.h) */
#define ps ((PItem *)pst.p)
#define nps (pst.n)
static const char **pn; static int pncap;
static void ppush(PKind k, Term *t, int depth, int prec, const char *str) {
    PItem it = { k, t, depth, prec, str }; STACK_PUSH(&pst, PItem, it);
}
static void pn_set(int d, const char *s) {
    if (d >= pncap) { int nc = pncap ? pncap : 256; while (nc <= d) nc *= 2; pn = rrealloc(pn, (size_t)nc * sizeof(char *)); memset(pn + pncap, 0, (size_t)(nc - pncap) * sizeof(char *)); pncap = nc; }
    pn[d] = s;
}
#define PT(t_, d_, p_) ppush(PT_TERM, (t_), (d_), (p_), NULL)
#define PS(s_) ppush(PT_STR, NULL, 0, 0, (s_))
#define PN(d_, s_) ppush(PT_NAME, NULL, (d_), 0, (s_))
/* a global's level: the hidden level + n reads as ^n */
static void ref_lvl_push(FILE *f, Term *t, int depth) {
    int hn;
    if (!t->a) return;
    if (t->a->k == T_LVAL && lv_is_hidden_plus(t->a->lvl, &hn)) { if (hn) { char *b = xalloc(24); snprintf(b, 24, "^%d", hn); PS(b); } return; }
    PS("^{"); PT(t->a, depth, 0); PS("}");
}
/* one term: a leaf is printed at once; otherwise its pieces are pushed in output order (then reversed onto the stack) */
static void tp_node(FILE *f, Term *t, int depth, int prec) {
    unsigned long long num;
    if ((t->k == T_APP || t->k == T_CON) && numeral_of(t, &num)) { fprintf(f, "%llu", num); return; }
    size_t from = nps;
    switch (t->k) {
    case T_VAR: {
        int lvl = depth - 1 - t->n;
        if (lvl >= 0 && lvl < depth && lvl < pncap && pn[lvl]) fprintf(f, "%s", pn[lvl]); else fprintf(f, "#%d", t->n);
        return; }
    case T_U: {
        int hn;
        fputs(t->pre ? "Pre" : "U", f);
        if (t->a && t->a->k == T_LVAL && lv_is_hidden_plus(t->a->lvl, &hn)) { if (hn) fprintf(f, " %d", hn); return; }   /* the hidden level + n reads as U n */
        if (t->a) { PS(" {"); PT(t->a, depth, 0); PS("}"); break; }
        if (t->n) fprintf(f, " %d", t->n);
        return; }
    case T_LEVEL: fputs("Level", f); return;
    case T_LZERO: fprintf(f, "%d", t->n); return;
    case T_LMETA: fprintf(f, "?%d", t->n); return;
    case T_META: fprintf(f, "?%d", t->n); return;
    case T_LSUC: {
        int atom = t->a->k == T_VAR || t->a->k == T_LZERO;
        if (prec > 1) PS("(");
        for (int i = 0; i < t->n; i++) PS(i + 1 < t->n || !atom ? "lsuc (" : "lsuc ");
        PT(t->a, depth, 0);
        for (int i = 0; i < t->n; i++) if (i + 1 < t->n || !atom) PS(")");
        if (prec > 1) PS(")");
        break; }
    case T_LMAX: if (prec > 0) PS("("); PS("lmax "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); if (prec > 0) PS(")"); break;
    case T_DEF: PS(defs[t->n].name); ref_lvl_push(f, t, depth); break;
    case T_DATA: PS(datas[t->n].name); ref_lvl_push(f, t, depth); break;
    case T_CON: PS(cons[t->n].name); ref_lvl_push(f, t, depth); break;
    case T_NUM: { char *str = bn_to_dec(t->num); fputs(str, f); free(str); return; }
    case T_IRR: fputc('.', f); return;
    case T_ELIM: PS("elim "); PS(datas[t->n].name); ref_lvl_push(f, t, depth); break;
    case T_LVAL: lv_tp(f, t->lvl, pn, depth < pncap ? depth : pncap, prec); return;
    case T_INTERVAL: fputs("I", f); return;
    case T_I0: fputs("i0", f); return;
    case T_I1: fputs("i1", f); return;
    case T_INEG: PS("~ "); PT(t->a, depth, 3); break;
    case T_IAND: if (prec > 0) PS("("); PT(t->a, depth, 1); PS(" /\\ "); PT(t->b, depth, 1); if (prec > 0) PS(")"); break;
    case T_IOR:  if (prec > 0) PS("("); PT(t->a, depth, 1); PS(" \\/ "); PT(t->b, depth, 1); if (prec > 0) PS(")"); break;
    case T_PI: {
        if (prec > 0) PS("(");
        const char *nm = t->name && strcmp(t->name, "_") ? t->name : NULL;
        if (nm) { PS(t->imp ? "{" : (t->irr & 2) ? ".(" : "("); PS(nm); PS(" : "); PT(t->a, depth, 0); PS(t->imp ? "} -> " : ") -> "); }
        else { PT(t->a, depth, 1); PS(" -> "); }
        PN(depth, nm ? nm : "_"); PT(t->b, depth + 1, 0);
        if (prec > 0) PS(")");
        break; }
    case T_SIGMA: {
        if (prec > 1) PS("(");
        PS("Sigma "); PT(t->a, depth, 2); PS(" (\\"); PS(t->name ? t->name : "_"); PS(" -> ");
        PN(depth, t->name ? t->name : "_"); PT(t->b, depth + 1, 0); PS(")");
        if (prec > 1) PS(")");
        break; }
    case T_PAIR: PS("("); PT(t->a, depth, 0); PS(" , "); PT(t->b, depth, 0); PS(")"); break;
    case T_FST: if (prec > 1) PS("("); PS("fst "); PT(t->a, depth, 2); if (prec > 1) PS(")"); break;
    case T_GLUE:
        if (prec > 1) PS("(");
        PS("Glue "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); PS(" "); PT(t->c, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_GLUEEL: if (prec > 1) PS("("); PS("glue "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); if (prec > 1) PS(")"); break;
    case T_UNGLUE: if (prec > 1) PS("("); PS("unglue "); PT(t->a, depth, 2); if (prec > 1) PS(")"); break;
    case T_SND: if (prec > 1) PS("("); PS("snd "); PT(t->a, depth, 2); if (prec > 1) PS(")"); break;
    case T_LAM: {
        if (prec > 0) PS("(");
        PS(t->imp ? "\\{" : "\\"); PS(t->name); PS(t->imp ? "} -> " : " -> "); PN(depth, t->name); PT(t->a, depth + 1, 0);
        if (prec > 0) PS(")");
        break; }
    case T_APP: case T_PAPP:
        if (prec > 1) PS("(");
        PT(t->a, depth, 1); PS(" "); PT(t->b, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_LET:
        if (prec > 0) PS("(");
        PS("let "); PS(t->name); PS(" : "); PT(t->a, depth, 0); PS(" := "); PT(t->b, depth, 0);
        PS(" in "); PN(depth, t->name); PT(t->c, depth + 1, 0);
        if (prec > 0) PS(")");
        break;
    case T_PATHP:
        if (prec > 1) PS("(");
        PS("PathP "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); PS(" "); PT(t->c, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_PARTIAL:
        if (prec > 1) PS("(");
        PS("Partial "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_TRANSP:
        if (prec > 1) PS("(");
        PS("transp "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); PS(" "); PT(t->c, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_HCOMP:
        if (prec > 1) PS("(");
        PS("hcomp "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); PS(" ");
        PT(t->c, depth, 2); PS(" "); PT(t->d, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_SUB:
        if (prec > 1) PS("(");
        PS("Sub "); PT(t->a, depth, 2); PS(" "); PT(t->b, depth, 2); PS(" "); PT(t->c, depth, 2);
        if (prec > 1) PS(")");
        break;
    case T_INS: if (prec > 1) PS("("); PS("inS "); PT(t->a, depth, 2); if (prec > 1) PS(")"); break;
    case T_OUTS: if (prec > 1) PS("("); PS("outS "); PT(t->d, depth, 2); if (prec > 1) PS(")"); break;
    case T_SYS:
        PS("[ ");
        for (int i = 0; i < t->nbr; i++) { if (i) PS(" | "); PT(t->br[i].face, depth, 0); PS(" -> "); PT(t->br[i].body, depth, 0); }
        PS(" ]");
        break;
    default: return;
    }
    if (nps > from) for (size_t i = from, j = nps - 1; i < j; i++, j--) { PItem x = ps[i]; ps[i] = ps[j]; ps[j] = x; }
}
void term_print(FILE *f, Term *t, const char **names, int depth) {
    for (int i = 0; i < depth; i++) pn_set(i, names[i]);
    size_t base = nps;
    PT(t, depth, 0);
    while (nps > base) {
        PItem it = ps[--nps];
        if (it.k == PT_STR) fputs(it.s, f);
        else if (it.k == PT_NAME) pn_set(it.depth, it.s);
        else tp_node(f, it.t, it.depth, it.prec);
    }
}
#undef PT
#undef PS
#undef PN

/* ---- interval algebra ---- */
static int lit_cmp(const void *a, const void *b) {
    const ILit *x = a, *y = b;
    if (x->var != y->var) return x->var - y->var;
    return x->neg - y->neg;
}
static IConj conj_norm(ILit *l, int n) {
    ILit *c = xalloc((n + 1) * sizeof(ILit)); memcpy(c, l, n * sizeof(ILit));
    qsort(c, n, sizeof(ILit), lit_cmp);
    int m = 0;
    for (int i = 0; i < n; i++) if (m == 0 || lit_cmp(&c[m - 1], &c[i])) c[m++] = c[i];
    IConj r = { c, m }; return r;
}
static int conj_subset(const IConj *a, const IConj *b) {     /* a ⊆ b */
    int j = 0;
    for (int i = 0; i < a->n; i++) {
        while (j < b->n && lit_cmp(&b->l[j], &a->l[i]) < 0) j++;
        if (j >= b->n || lit_cmp(&b->l[j], &a->l[i]) != 0) return 0;
    }
    return 1;
}
static int conj_cmp(const void *a, const void *b) {
    const IConj *x = a, *y = b;
    if (x->n != y->n) return x->n - y->n;
    for (int i = 0; i < x->n; i++) { int c = lit_cmp(&x->l[i], &y->l[i]); if (c) return c; }
    return 0;
}
static IVal dnf_norm(IConj *cs, int n) {       /* absorption + dedupe + sort */
    int *keep = xalloc((n + 1) * sizeof(int));
    for (int i = 0; i < n; i++) keep[i] = 1;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        if (i == j || !keep[i] || !keep[j]) continue;
        if (conj_subset(&cs[j], &cs[i]) && (cs[j].n < cs[i].n || j < i)) { keep[i] = 0; }
    }
    IConj *out = xalloc((n + 1) * sizeof(IConj)); int m = 0;
    for (int i = 0; i < n; i++) if (keep[i]) out[m++] = cs[i];
    qsort(out, m, sizeof(IConj), conj_cmp);
    IVal r = { out, m }; return r;
}
IVal iv_zero(void) { IVal r = { NULL, 0 }; return r; }
IVal iv_one(void) { IConj *c = xalloc(sizeof(IConj)); c[0].l = NULL; c[0].n = 0; IVal r = { c, 1 }; return r; }
IVal iv_var(int level) { ILit l = { level, 0 }; IConj *c = xalloc(sizeof(IConj)); c[0] = conj_norm(&l, 1); IVal r = { c, 1 }; return r; }
IVal iv_or(IVal a, IVal b) {
    IConj *cs = xalloc((a.n + b.n + 1) * sizeof(IConj));
    for (int i = 0; i < a.n; i++) cs[i] = a.c[i];
    for (int i = 0; i < b.n; i++) cs[a.n + i] = b.c[i];
    return dnf_norm(cs, a.n + b.n);
}
IVal iv_and(IVal a, IVal b) {
    IConj *cs = xalloc((a.n * b.n + 1) * sizeof(IConj)); int m = 0;
    for (int i = 0; i < a.n; i++) for (int j = 0; j < b.n; j++) {
        ILit *l = xalloc((a.c[i].n + b.c[j].n + 1) * sizeof(ILit));
        memcpy(l, a.c[i].l, a.c[i].n * sizeof(ILit)); memcpy(l + a.c[i].n, b.c[j].l, b.c[j].n * sizeof(ILit));
        cs[m++] = conj_norm(l, a.c[i].n + b.c[j].n);
    }
    return dnf_norm(cs, m);
}
IVal iv_neg(IVal a) {
    IVal r = iv_one();
    for (int i = 0; i < a.n; i++) {             /* neg(c1 ∨ c2 ...) = neg c1 ∧ neg c2 ...; neg(l1 ∧ l2 ..) = neg l1 ∨ neg l2 .. */
        IVal d = iv_zero();
        for (int j = 0; j < a.c[i].n; j++) {
            ILit l = { a.c[i].l[j].var, !a.c[i].l[j].neg };
            IConj *c = xalloc(sizeof(IConj)); c[0] = conj_norm(&l, 1); IVal lv = { c, 1 };
            d = iv_or(d, lv);
        }
        r = iv_and(r, d);
    }
    return r;
}
int iv_is_one(IVal a) { return a.n == 1 && a.c[0].n == 0; }
int iv_is_zero(IVal a) { return a.n == 0; }
int iv_eq(IVal a, IVal b) {
    if (a.n != b.n) return 0;
    for (int i = 0; i < a.n; i++) if (conj_cmp(&a.c[i], &b.c[i])) return 0;
    return 1;
}
int iv_mentions(IVal a, int level) {
    for (int i = 0; i < a.n; i++) for (int j = 0; j < a.c[i].n; j++) if (a.c[i].l[j].var == level) return 1;
    return 0;
}
static int face_lookup(const Face *f, int var) { for (int i = 0; i < f->n; i++) if (f->var[i] == var) return f->val[i]; return -1; }
IVal iv_restrict(IVal a, const Face *f) {
    IConj *cs = xalloc((a.n + 1) * sizeof(IConj)); int m = 0;
    for (int i = 0; i < a.n; i++) {
        ILit *l = xalloc((a.c[i].n + 1) * sizeof(ILit)); int n = 0, dead = 0;
        for (int j = 0; j < a.c[i].n; j++) {
            int v = face_lookup(f, a.c[i].l[j].var);
            if (v < 0) { l[n++] = a.c[i].l[j]; continue; }
            int value = a.c[i].l[j].neg ? !v : v;
            if (!value) { dead = 1; break; }
        }
        if (!dead) cs[m++] = conj_norm(l, n);
    }
    return dnf_norm(cs, m);
}
IVal iv_subst(IVal a, int var, IVal s) {
    IVal r = iv_zero();
    for (int i = 0; i < a.n; i++) {
        IVal c = iv_one();
        for (int j = 0; j < a.c[i].n; j++) {
            ILit l = a.c[i].l[j]; IVal lv;
            if (l.var == var) lv = l.neg ? iv_neg(s) : s;
            else { IConj *cj = xalloc(sizeof(IConj)); cj[0] = conj_norm(&l, 1); IVal t = { cj, 1 }; lv = t; }
            c = iv_and(c, lv);
        }
        r = iv_or(r, c);
    }
    return r;
}
IVal iv_forall(IVal a, int var) {        /* keep the conjuncts that do not mention var */
    IConj *cs = xalloc((a.n + 1) * sizeof(IConj)); int m = 0;
    for (int i = 0; i < a.n; i++) {
        int mentions = 0;
        for (int j = 0; j < a.c[i].n; j++) if (a.c[i].l[j].var == var) mentions = 1;
        if (!mentions) cs[m++] = a.c[i];
    }
    return dnf_norm(cs, m);
}
static IVal face_iv(const Face *f) {
    IVal r = iv_one();
    for (int i = 0; i < f->n; i++) { IVal l = iv_var(f->var[i]); if (!f->val[i]) l = iv_neg(l); r = iv_and(r, l); }
    return r;
}
int iv_faces(IVal phi, Face **out) {
    Face *fs = xalloc((phi.n + 1) * sizeof(Face)); int m = 0;
    for (int i = 0; i < phi.n; i++) {
        Face f; f.n = 0; f.var = xalloc((phi.c[i].n + 1) * sizeof(int)); f.val = xalloc((phi.c[i].n + 1) * sizeof(int));
        int ok = 1;
        for (int j = 0; j < phi.c[i].n; j++) {
            int var = phi.c[i].l[j].var, val = !phi.c[i].l[j].neg;
            int prev = face_lookup(&f, var);
            if (prev >= 0) { if (prev != val) { ok = 0; break; } continue; }
            f.var[f.n] = var; f.val[f.n] = val; f.n++;
        }
        if (ok) fs[m++] = f;
    }
    *out = fs; return m;
}
Face face_join(const Face *a, const Face *b) {
    Face f; f.n = 0; f.var = xalloc((a->n + b->n + 1) * sizeof(int)); f.val = xalloc((a->n + b->n + 1) * sizeof(int));
    for (int i = 0; i < a->n; i++) { f.var[f.n] = a->var[i]; f.val[f.n] = a->val[i]; f.n++; }
    for (int i = 0; i < b->n; i++) {
        int prev = face_lookup(&f, b->var[i]);
        if (prev >= 0) { if (prev != b->val[i]) { f.n = -1; return f; } continue; }
        f.var[f.n] = b->var[i]; f.val[f.n] = b->val[i]; f.n++;
    }
    return f;
}

/* ---- values ---- */
void vl_push_arg(VList *l, Arg a) {
    if (l->n == l->cap) { int c = l->cap ? 2 * l->cap : 4; Arg *na = xalloc(c * sizeof(Arg)); if (l->n) memcpy(na, l->a, l->n * sizeof(Arg)); l->a = na; l->cap = c; }
    l->a[l->n++] = a;
}
void vl_push(VList *l, Val *v, int irr) { Arg a = {0}; a.v = v; a.irr = irr; vl_push_arg(l, a); }
VList vl_copy(const VList *l) { VList r = {0}; for (int i = 0; i < l->n; i++) vl_push_arg(&r, l->a[i]); return r; }
Env *env_push(Env *e, Val *v) { Env *n = xalloc(sizeof *n); n->v = v; n->next = e; return n; }
Val *env_get(Env *e, int idx) { while (idx-- > 0) { if (!e) die("internal: unbound variable"); e = e->next; } if (!e) die("internal: unbound variable"); return e->v; }

Val *mkval(VKind k) { Val *v = xalloc(sizeof *v); v->k = k; return v; }
Val *vvar(int level) { Val *v = mkval(V_NEU); v->h = H_VAR; v->n = level; return v; }
Val *vu_l(LVal l) { Val *v = mkval(V_U); v->lvl = l; return v; }
Val *vupre_l(LVal l) { Val *v = vu_l(l); v->pre = 1; return v; }
Val *vu(int l) { return vu_l(lv_const(l)); }
Val *vupre(int l) { return vupre_l(lv_const(l)); }
Val *vl(LVal l) { Val *v = mkval(V_L); v->lvl = l; return v; }
Val *vlvar(int level) { return vl(lv_var(level)); }
Val *vlevel(void) { return mkval(V_LEVEL); }
LVal eval_level(Env *env, Term *t) {
    switch (t->k) {
    case T_LZERO: return lv_const(t->n);
    case T_LVAL: return t->lvl;
    case T_LMETA: return lv_meta(t->n);
    case T_LSUC: return lv_add(eval_level(env, t->a), t->n);
    case T_LMAX: return lv_max(eval_level(env, t->a), eval_level(env, t->b));
    default: {
        Val *v = eval(env, t);
        if (v->k == V_L) return v->lvl;
        if (v->k == V_NEU && v->h == H_VAR && v->args.n == 0) return lv_var(v->n);
        die("internal: a level evaluated to a non-level");
        return lv_const(0);
    }
    }
}
Term *quote_level(int depth, LVal l) {
    Term *r = NULL;
    for (int i = 0; i < l.n; i++) {
        Term *x;
        if (l.t[i].meta) { x = mk_term(T_LMETA, NULL, NULL, NULL, NULL); x->n = l.t[i].var; }
        else if (l.t[i].var == -1) { LVal h = lv_var(-1); h.t[0].off = l.t[i].off; x = mk_lval(h); continue_hidden: r = r ? mk_term(T_LMAX, r, x, NULL, NULL) : x; continue; }
        else x = mk_var(depth - 1 - l.t[i].var);
        if (l.t[i].off) { Term *s = mk_term(T_LSUC, x, NULL, NULL, NULL); s->n = l.t[i].off; x = s; }
        if (0) goto continue_hidden;
        r = r ? mk_term(T_LMAX, r, x, NULL, NULL) : x;
    }
    if (l.c || !r) { Term *z = mk_term(T_LZERO, NULL, NULL, NULL, NULL); z->n = l.c; r = r ? mk_term(T_LMAX, r, z, NULL, NULL) : z; }
    return r;
}
Val *vi(IVal iv) { Val *v = mkval(V_I); v->iv = iv; return v; }
Val *vivar(int level) { return vi(iv_var(level)); }
static Val *vinterval(void) { return mkval(V_INTERVAL); }
static int fresh_level = 1 << 20;      /* scratch interval variables, never in a context */
static Val *fresh_ivar(void) { return vivar(fresh_level++); }

/* native closures: a code and captured values */
enum { N_IH = 1, N_LINE_DOM, N_LINE_COD_V, N_TRANSP_V, N_LINE_IOR, N_LINE_IAND, N_HCOMP_PI_SIDES, N_PATH_HCOMP_SIDES,
       N_LINE_PATH_AT, N_PATH_TRANSP_SIDES, N_FWD_SIDES, N_FILL, N_FILL_SIDES, N_TFILL, N_DATA_ARG_LINE, N_SYS_PROJ,
       N_CONST, N_ELIM_MOTIVE_LINE, N_ELIM_SIDES,
       N_SUBST, N_GLUE_T, N_UNGLUE_U0, N_GLUE_TR_SIDES, N_GLUE_A1P_SIDES, N_GLUE_HF, N_GLUE_HC_SIDES, N_GCOMP_SIDES,
       N_ELIM_PATH_IH, N_TRANSP_MAP, N_HITTR_SIDES };
typedef struct { int code; int i1, i2, i3; VList cap;  LVal l;
                 Val *marg, *mres; int mmv, mon, mstable; } Native;   /* one-entry application memo: the last argument and at which metas version */
typedef struct { int n; Val *v[8]; LVal l; } Caps;

static Val *native_apply(Native *nt, Val *arg);
static Val *native_step(Native *nt, Val *arg);
typedef struct { Val *psi, *forall, *ungl, *Teg, *tf, *i; int F; } TrSides;
typedef struct { Val *phi1, *psi, *alphas, *ts, *Te1, *a1, *j; } A1pData;
typedef struct { Val *Te, *psi, *u, *u0, *i; } HfData;
typedef struct { Val *Ab, *phi, *Te, *psi, *u, *tfs, *i; } HcData;
typedef Val *(*SysBody)(int k, const Face *f, void *data);
static Val *vsys_faces(int nb, Val **phis, SysBody body, void *data);
static Val *glue_tr_body(int k, const Face *f, void *data);
static Val *glue_a1p_body(int k, const Face *f, void *data);
static Val *glue_hf_body(int k, const Face *f, void *data);
static Val *glue_hc_body(int k, const Face *f, void *data);
static Val *gcomp_body(int k, const Face *f, void *data);
static Val *transp_glue(Val *line, Val *psi, Val *u0, Val *Ag, Val *fiv);
static Val *hcomp_glue(Val *A, Val *psi, Val *u, Val *u0);
static Val *hcompU_body(int k, const Face *f, void *data);
static Val *builtin_at(const char *name, LVal L);
static Val *vfwd(Val *line, Val *r, Val *u);
static Val *vtfill(Val *line, Val *phi, Val *u0);
static Val *nfn(void *data, Val *arg) { return native_apply(data, arg); }
static Val *vnative(int code, int i1, int i2, int i3, int ncap, ...) {
    Native *nt = xalloc(sizeof *nt); nt->code = code; nt->i1 = i1; nt->i2 = i2; nt->i3 = i3;
    va_list ap; va_start(ap, ncap);
    for (int i = 0; i < ncap; i++) vl_push(&nt->cap, va_arg(ap, Val *), 0);
    va_end(ap);
    Val *v = mkval(V_LAM); v->clo.fn = nfn; v->clo.data = nt; v->name = "i"; v->isi = 1;
    return v;
}
Val *vlam_native(const char *name, Val *(*fn)(void *, Val *), void *data) { Val *v = mkval(V_LAM); v->clo.fn = fn; v->clo.data = data; v->name = name; return v; }

static Val *neu_app(Val *f, Arg a) {
    Val *v = mkval(f->k); *v = *f; v->args = vl_copy(&f->args); vl_push_arg(&v->args, a);
    v->unf = NULL; v->unf_n = 0; v->unf_mv = 0;   /* a longer spine: the copied memo, if any, does not apply */
    v->par = f;                                    /* but the parent's does, for all but the last entry */
    return v;
}

/* ---- literals (M15) ---- */
Term *mk_num(int d, Term *lt, Bn *n) { Term *t = mk_term(T_NUM, lt, NULL, NULL, NULL); t->n = d; t->num = n; return t; }
Val *vnum(int d, LVal l, Bn *n) { Val *v = mkval(V_NUM); v->n = d; v->lvl = l; v->num = n; return v; }
Val *num_view(Val *v) {
    int zi, si;
    if (!peano_shape(v->n, &zi, &si)) die("internal: a literal of a type not shaped like the naturals");
    Val *c = mkval(V_CON); c->lvl = v->lvl;
    if (bn_is_zero(v->num)) { c->n = zi; return c; }
    c->n = si;
    Arg ar = {0}; ar.v = vnum(v->n, v->lvl, bn_pred(v->num));
    return neu_app(c, ar);
}
static const char *native_names[] = { "add", "sub", "mul", "div", "mod", "pow", "beq", "blt", "ble", "minv" };
int native_code(const char *name) { for (int i = 0; i < 10; i++) if (!strcmp(name, native_names[i])) return i + 1; return 0; }
static Bn *nat_op(int code, const Bn *a, const Bn *b) {
    Bn *q, *r;
    switch (code) {
    case 1: return bn_add(a, b);
    case 2: return bn_monus(a, b);
    case 3: return bn_mul(a, b);
    case 4: bn_divmod(a, b, &q, &r); return q;
    case 5: bn_divmod(a, b, &q, &r); return r;
    case 6: return bn_pow(a, b);
    case 7: return bn_from_u64(bn_cmp(a, b) == 0);
    case 8: return bn_from_u64(bn_cmp(a, b) < 0);
    case 9: return bn_from_u64(bn_cmp(a, b) <= 0);
    case 10: return bn_minv(a, b);   /* the modular inverse: the power is taken modulo y, never built */
    }
    die("internal: unknown native %d", code); return NULL;
}
static char last_fallback[2][64]; static int last_fallback_code;
static long fb_count[16]; static char fb_first[16][2][64];
void fallback_report(void) {
    if (!getenv("EEZOTT_TRIPWIRE_METHODS")) return;
    fprintf(stderr, "  native fallbacks by code (1 add 2 sub 3 mul 4 div 5 mod 6 pow 7 eq 8 lt 9 le 10 minv):\n");
    for (int c = 1; c <= 10; c++) if (fb_count[c]) fprintf(stderr, "    code %d: %ld  first: arg1 = %s; arg2 = %s\n", c, fb_count[c], fb_first[c][0], fb_first[c][1]);
}
typedef struct { int code, d, def; Val *fallback, *arg1; } NatNative;   /* def: the native's definition (the head of its guard neutral) */
static Val *natfn(void *data, Val *arg) {
    NatNative *nn = data;
    if (!nn->arg1) { NatNative *m = xalloc(sizeof *m); *m = *nn; m->arg1 = arg; return vlam_native("n", natfn, m); }
    Val *a = force(nn->arg1), *b = force(arg);
    if (a->k == V_NUM && b->k == V_NUM && a->n == nn->d && b->n == nn->d) {
        /* pow is the one native whose result may be a number no limb list can hold (M17). When it is, the
           kernel does not compute it and does not unfold it either: the native application itself stands, a
           rigid neutral whose unfolding is itself - canonical enough for force, opaque to conversion (the same
           power compares by its spine), and the laws (pow_add, pow_mul) prove what it cannot compute. Lean's
           pow guard (S2). An elimination on it, or a native over it, stays a neutral: no canonical form exists. */
        if (nn->code == 6 && !bn_fits_pow(a->num, b->num)) {
            Val *v = mkval(V_NEU); v->h = H_DEF; v->n = nn->def; v->lvl = a->lvl;
            Arg x = {0}; x.v = nn->arg1; v = neu_app(v, x); x.v = arg; v = neu_app(v, x);
            v->unf = v; v->unf_n = v->args.n; v->unf_stable = 1;
            return v;
        }
        return vnum(nn->d, a->lvl, nat_op(nn->code, a->num, b->num));
    }
    static int diag = -1; if (diag < 0) diag = getenv("EEZOTT_TRIPWIRE_METHODS") != NULL;
    if (diag) {   /* the last native that fell back to its body, for the tripwire's diagnostic */
        fb_count[nn->code]++;
        Val *x[2] = { a, b };
        for (int i = 0; i < 2; i++) {
            Val *v = x[i]; int k = 0; char *d = NULL;
            while (v->k == V_CON && v->args.n == 1 && k < 100000) { v = force(v->args.a[0].v); k++; }
            if (v->k == V_NUM) d = bn_to_dec(v->num);
            snprintf(last_fallback[i], 64, "%s%s+%d sucs, core kind %d%s%s", d ? "lit " : "", d ? d : "", k, v->k,
                     v->k == V_NEU ? " head " : "", v->k == V_NEU ? (v->h == H_DEF ? defs[v->n].name : v->h == H_VAR ? "var" : v->h == H_ELIM ? "elim" : "other") : "");
            free(d);
        }
        last_fallback_code = nn->code;
        if (!fb_first[nn->code][0][0]) { snprintf(fb_first[nn->code][0], 64, "%s", last_fallback[0]); snprintf(fb_first[nn->code][1], 64, "%s", last_fallback[1]); }
    }
    return vapp(vapp(nn->fallback, nn->arg1, 0), arg, 0);
}
Val *native_wrapper(int code, int d, Val *fallback, int def) {
    NatNative *nn = xalloc(sizeof *nn); nn->code = code; nn->d = d; nn->def = def; nn->fallback = fallback; nn->arg1 = NULL;
    return vlam_native("m", natfn, nn);
}
static Val *elim_apply_list(int data, VList *args);

/* ---- induction hypotheses (native closure N_IH) ----
   cap = base (params, motive, methods), tele (params, previous args), ys, aj; i1=data i2=con i3=j; ys count = cap.n - nb - nt - 1 */
static Val *ih_apply(Native *c, Val *y);
static Val *motive_applied(int data, VList *pre, Val **idx);

/* iota: the eliminator's full spine ends in a constructor */
static int elim_data_cur;
static Val *elim_of_branch(Val *b, void *data);
static Val *vsys(VBranch *br, int n);
static Val *vsys_map(Val *sys, Val *(*fn)(Val *, void *), void *data);
/* a term's heads only, for the tripwire's diagnostic: names of globals, binders as a backslash, variables by index */
static void term_heads(FILE *f, Term *t, int d) {
    if (!t) { fputs("_", f); return; }
    if (d > 6) { fputs("..", f); return; }
    switch (t->k) {
    case T_VAR: fprintf(f, "v%d", t->n); break;
    case T_DEF: fprintf(f, "%s", defs[t->n].name); break;
    case T_CON: fprintf(f, "%s", cons[t->n].name); break;
    case T_DATA: fprintf(f, "%s", datas[t->n].name); break;
    case T_ELIM: fprintf(f, "elim %s", datas[t->n].name); break;
    case T_LAM: fputs("\\ ", f); term_heads(f, t->a, d + 1); break;
    case T_APP: fputc('(', f); term_heads(f, t->a, d + 1); fputc(' ', f); term_heads(f, t->b, d + 1); fputc(')', f); break;
    case T_NUM: { char *s = bn_to_dec(t->num); fputs(s, f); free(s); break; }
    default: fprintf(f, "<k%d>", t->k); break;
    }
}
/* The literal-elimination tripwire. A method that uses its induction hypothesis walks the literal a step at a
   time, so a walk over a machine-sized literal is work proportional to the literal - 1e19 steps at the word
   bounds. What it must count is NESTING: a walk nests (the branch forces its induction hypothesis inside this
   call), while a program that merely uses many literals does not. Counted as a running total instead, the
   tripwire fires on the 66th innocent use of a literal anywhere in the run, and names an innocent walker.
   Eliminations reduce on demand (elim_force), so a walk starts only where a native or an elimination forces the
   hypothesis inside the step; a walk that conversion drives from outside is iterative and meets the resource
   limits instead - the checker's own elimination, work proportional to the value, as Lean's and Agda's (S2). */
static int elim_num_depth;
static struct { int data; char lit[16]; } elim_trace[64];   /* the nesting chain's first 64 levels, for the tripwire's diagnostic */
static Val *elim_of_branch(Val *b, void *data) { VList a2 = vl_copy((VList *)data); vl_push(&a2, b, 0); return elim_apply_list(elim_data_cur, &a2); }

/* the eliminator through a formal composition (a normal form on indexed families, and on HITs later):
     elim D p P m idx (hcomp A phi u u0) = comp (\k. P idx (hfill A phi u u0 k)) phi (\k. elim .. (u k)) (elim .. u0)   */
static Val *vcomp(Val *line, Val *phi, Val *u, Val *u0);
static Val *apply_to(Val *b, void *E) { return vapp((Val *)E, b, 0); }
static Val *elim_hcomp(int data, VList *args) {
    Data *D = &datas[data];
    int np = D->nparams, nb = D->nblock, K = block_ncons(data), m = D->nidx;
    Val *t = force(args->a[args->n - 1].v);
    if (t->k != V_NEU || t->h != H_HCOMP || t->a->k != V_DATA || t->a->n != data) return NULL;
    Val *E = mkval(V_NEU); E->h = H_ELIM; E->n = data; E->lvl = elim_lvl;
    for (int i = 0; i < args->n - 1; i++) E = vapp(E, args->a[i].v, args->a[i].irr);
    Native *nt = xalloc(sizeof *nt); nt->code = N_ELIM_MOTIVE_LINE; nt->i1 = 0;   /* the motive at the indices (and their images), then the filler */
    Val **iv = xalloc((m + 1) * sizeof(Val *));
    for (int j = 0; j < m; j++) iv[j] = args->a[np + nb + K + j].v;
    vl_push(&nt->cap, motive_applied(data, args, iv), 0);
    vl_push(&nt->cap, vnative(N_FILL, 1, 0, 0, 4, t->a, t->b, t->c, t->dom), 0);
    Val *line = mkval(V_LAM); line->clo.fn = nfn; line->clo.data = nt; line->isi = 1; line->name = "k";
    return vcomp(line, t->b, vnative(N_ELIM_SIDES, 0, 0, 0, 2, E, t->c), vapp(E, t->dom, 0));
}
/* ---- systems (partial elements) ---- */
static Val *vsys(VBranch *br, int n) {
    for (int i = 0; i < n; i++) if (iv_is_one(br[i].phi->iv)) return br[i].v;   /* a total branch: the element itself */
    Val *v = mkval(V_SYS); v->br = xalloc((n + 1) * sizeof(VBranch)); v->nbr = 0;
    for (int i = 0; i < n; i++) if (!iv_is_zero(br[i].phi->iv)) v->br[v->nbr++] = br[i];
    return v;
}
Val *vsys_at(Val *sys, const Face *f) {
    if (sys->k != V_SYS) return sys;                     /* total element, or a neutral partial element */
    for (int i = 0; i < sys->nbr; i++) {
        IVal p = f ? iv_restrict(sys->br[i].phi->iv, f) : sys->br[i].phi->iv;
        if (iv_is_one(p)) return f ? restrict_val(sys->br[i].v, f) : sys->br[i].v;
    }
    return NULL;
}
/* apply a function to every branch of a partial element (or to the element itself if it is total / neutral) */
static Val *vsys_map(Val *sys, Val *(*fn)(Val *, void *), void *data) {
    if (sys->k != V_SYS) return fn(sys, data);
    VBranch *br = xalloc((sys->nbr + 1) * sizeof(VBranch));
    for (int i = 0; i < sys->nbr; i++) { br[i].phi = sys->br[i].phi; br[i].v = fn(sys->br[i].v, data); }
    return vsys(br, sys->nbr);
}

/* cubical subtypes: outS (inS x) = x, and outS s = u when phi holds */
Val *vouts(Val *A, Val *phi, Val *u, Val *s) {
    if (iv_is_one(phi->iv)) { Val *t = vsys_at(u, NULL); if (t) return t; }
    s = force(s);   /* through a rigid definition application (the H_DEF plan): outS s with s := inS a is a, not a normal form (M20 F4 found it) */
    if (s->k == V_INS) return s->a;
    Val *v = mkval(V_NEU); v->h = H_OUTS; v->a = A; v->b = phi; v->c = u; v->dom = s; return v;
}

/* ---- application ---- */
static long *unf_count;   /* diagnostic: how many times each definition's body was evaluated (EEZOTT_UNFOLD_COUNTS) */
void unfold_counts_report(void) {
    if (!unf_count) return;
    fprintf(stderr, "  unfoldings per definition (top):\n");
    for (int k = 0; k < 12; k++) { int best = -1; for (int i = 0; i < ndefs; i++) if (unf_count[i] > 0 && (best < 0 || unf_count[i] > unf_count[best])) best = i;
        if (best < 0) break; fprintf(stderr, "    %8ld  %s\n", unf_count[best], defs[best].name); unf_count[best] = -unf_count[best]; }
}

/* ---- evaluation ---- */
static IVal face_iv(const Face *f);
/* ---- the machine (S3) ----
   Evaluation is an explicit machine, not C recursion (Order_Lev_EezottIterative): every activation of a function in
   the evaluator's knot is a frame on one heap stack, its locals that outlive a call kept in the frame, and a driver
   loop runs the top frame's step. A step either returns a value (its frame popped, the value in mret, the frame below
   resumed at the point it left) or pushes a callee and returns to the driver. So an evaluation's depth is bounded by
   memory alone. The C entry points (eval, vapp, inst, ...) push a frame and run the driver until it returns: callers
   not yet on the machine nest a driver run, nothing else does.
   A step never holds a pointer to its frame across anything that may push (the stack may move): F re-derives it from
   the frame's offset each time. The resume points are case labels of the frame's pc (Duff's device); a step whose
   case would have one inside another switch hands its frame over to a step of its own (MBECOME). */
typedef struct { void (*step)(size_t); int pc; size_t prev; } MHdr;
static Stack mst = { NULL, 0, 0, 1 };
static size_t mtop = (size_t)-1;
static Val *mret;
static void *mpush(size_t size, void (*step)(size_t)) {
    size = (size + 15) & ~(size_t)15;
    size_t off = (mst.n + 15) & ~(size_t)15;
    stack_reserve(&mst, off + size);
    mst.n = off + size;
    MHdr *h = (MHdr *)(mst.p + off);
    memset(h, 0, size);
    h->step = step; h->prev = mtop;
    mtop = off;
    return h;
}
static void mpop(size_t off) { mtop = ((MHdr *)(mst.p + off))->prev; mst.n = off; }
/* run the frame just pushed, and all it calls, to its value */
static Val *mrun(void) {
    size_t below = ((MHdr *)(mst.p + mtop))->prev;
    while (mtop != below) { size_t off = mtop; ((MHdr *)(mst.p + off))->step(off); }
    return mret;
}
#define MSTART switch (F->h.pc) { case 0:;
#define MFINISH } return;
#define MCALL(push) MCALL_((push), __COUNTER__ + 1)   /* a resume point: a number unique in the file, never 0 */
#define MCALL_(push, n) do { F->h.pc = (n); push; return; case (n):; } while (0)
#define MRET(v) do { Val *mr_ = (v); mret = mr_; mpop(off); return; } while (0)
#define MTAIL(push) do { mpop(off); push; return; } while (0)   /* the callee's value is this frame's: its caller resumes */
#define MBECOME(st) do { F->h.step = (st); F->h.pc = 0; return; } while (0)
static int meta_solved_head(Val *v) { return v->k == V_NEU && v->h == H_META && tmetas[v->n].sol; }
static int force_needed(Val *v) { return meta_solved_head(v) || (v->k == V_NEU && (v->h == H_DEF || (v->h == H_ELIM && v->defer))); }
static void mpush_fmeta(Val *v);
static void mpush_force(Val *v);
static void mpush_unfold_def(Val *v);
static void mpush_elim_force(Val *v);
/* a field resolved through solved metas, or forced, on the machine (field is an F-> lvalue) */
#define MFMETA(field) do { if (meta_solved_head(field)) { MCALL(mpush_fmeta(field)); field = mret; } } while (0)
#define MFORCE(field) do { if (force_needed(field)) { MCALL(mpush_force(field)); field = mret; } } while (0)

static void mpush_eval(Env *env, Term *t);
static void mpush_vapp(Val *f, Val *a, int irr);
static void mpush_inst(Clo *c, Val *v);
static void mpush_vpapp(Val *p, Val *r, Val *x, Val *y);
static void mpush_vproj(Val *p, int which);
static void mpush_pair_snd(Val *p);
static void mpush_ih_apply(Native *c, Val *y);
static void mpush_subst_env(Env *e, Env **dst, int lv, IVal s);
static void mpush_apply_arg(Val *f, Arg *a) {
    if (a->proj) mpush_vproj(f, a->proj);
    else if (a->papp) mpush_vpapp(f, a->v, a->x, a->y);
    else mpush_vapp(f, a->v, a->irr);
}

/* inst: a closure applied. One-entry application memo (the memoization pass): a closure applied to the same value
   again is the same value, and branch bodies do apply the same closure to the same value repeatedly - baddGo's column
   uses its induction hypothesis three times, and each application re-ran the whole recursive fold, which made the
   fold's cost 3^columns (Finding_Eezott_EvalNoSharing_2026_09_14). The metas version guards it: a meta solved in
   between can resume a reduction that the first application took as neutral. */
typedef struct { MHdr h; Clo *c; Val *v; int save; } InstF;
static void inst_step(size_t off);
static void mpush_inst(Clo *c, Val *v) { InstF *f = mpush(sizeof *f, inst_step); f->c = c; f->v = v; }
#define F ((InstF *)(mst.p + off))
static void inst_step(size_t off) {
    MSTART
    { Clo *c = F->c;
      if (c->ires && c->iarg == F->v && (c->imv == metas_version || c->istable)) MRET(c->ires); }
    F->save = meta_blocked; meta_blocked = 0;
    if (F->c->fn == nfn && ((Native *)F->c->data)->code == N_IH && !((Native *)F->c->data)->mon) {
        MCALL(mpush_ih_apply(F->c->data, F->v));   /* an induction hypothesis on the machine (the memo is native_apply's: first use) */
    } else if (F->c->fn) mret = F->c->fn(F->c->data, F->v);
    else MCALL(mpush_eval(env_push(F->c->env, F->v), F->c->t));
    { Clo *c = F->c; Val *r = mret;
      c->iarg = F->v; c->ires = r; c->imv = metas_version; c->istable = !meta_blocked;
      meta_blocked |= F->save;
      MRET(r); }
    MFINISH
}
#undef F
Val *inst(Clo *c, Val *v) { mpush_inst(c, v); return mrun(); }

/* ---- application ---- */
typedef struct { MHdr h; Val *f, *a; int irr, i; Val *v, *av; VBranch *br; } VappF;
static void vapp_step(size_t off);
static void mpush_vapp(Val *f, Val *a, int irr) { VappF *x = mpush(sizeof *x, vapp_step); x->f = f; x->a = a; x->irr = irr; }
#define F ((VappF *)(mst.p + off))
static void vapp_step(size_t off) {
    MSTART
    MFMETA(F->f);   /* a definition application stays rigid here; force() unfolds it where a canonical form is needed */
    { Val *f = F->f; Arg ar = {0}; ar.v = F->a; ar.irr = F->irr;
      if (f->k == V_LAM) MTAIL(mpush_inst(&f->clo, ar.v));
      if (f->k == V_NEU) {
          if (f->h == H_ELIM) {
              Val *v = neu_app(f, ar);
              Data *D = &datas[f->n];
              int arity = D->nparams + D->nblock + block_ncons(f->n) + D->nidx + 1;
              if (v->args.n == arity) v->defer = 1;   /* saturated: reduced on demand (elim_force), call by need */
              MRET(v);
          }
          MRET(neu_app(f, ar));
      }
      if (f->k == V_DATA) MRET(neu_app(f, ar));
      if (f->k != V_CON && f->k != V_SYS) die("internal: application of a non-function value (kind %d)", f->k); }
    if (F->f->k == V_CON) {
        /* suc of a literal is the literal above - when the argument already is one. It is not forced here: under
           call by need the argument of suc is an induction hypothesis more often than not, and forcing it walked
           the literal the elimination was deferred on (Fix_Eezott_VappConForcedItsArgument, S2). */
        F->av = F->a; MFMETA(F->av);
        while (F->av->k == V_NEU && F->av->h == H_DEF) {   /* through definitions (memoised), not through deferred eliminations */
            MCALL(mpush_unfold_def(F->av)); F->v = mret; MFMETA(F->v);
            if (F->v == F->av) break;
            F->av = F->v;
        }
        { Val *av = F->av; Val *f = F->f;
          if (av->k == V_NUM && f->args.n == 0 && cons[f->n].data == av->n) {
              int zi, si;
              if (peano_shape(av->n, &zi, &si) && f->n == si) MRET(vnum(av->n, av->lvl, bn_succ(av->num)));
          }
          Arg ar = {0}; ar.v = F->a; ar.irr = F->irr;
          F->v = neu_app(f, ar); }
        { Con *C = con_at(F->f->n, F->f->lvl); int np = datas[C->data].nparams; Val *v = F->v;
          if (!(C->nint > 0 && v->args.n == np + C->nargs + C->nint) || !C->boundary) MRET(v);   /* a path constructor on a face of its boundary is the boundary */
          Env *env = NULL;
          for (int i = 0; i < v->args.n; i++) env = env_push(env, v->args.a[i].v);
          MCALL(mpush_eval(env, C->boundary)); }
        { Val *b = mret; if (b && b->k != V_SYS) MRET(b); MRET(F->v); }
    }
    /* a partial function applied pointwise */
    F->br = xalloc((F->f->nbr + 1) * sizeof(VBranch));
    for (F->i = 0; F->i < F->f->nbr; F->i++) {
        F->br[F->i].phi = F->f->br[F->i].phi;
        MCALL(mpush_vapp(F->f->br[F->i].v, F->a, F->irr));
        F->br[F->i].v = mret;
    }
    MRET(vsys(F->br, F->f->nbr));
    MFINISH
}
#undef F
Val *vapp(Val *f, Val *a, int irr) { mpush_vapp(f, a, irr); return mrun(); }

typedef struct { MHdr h; Val *p, *r, *x, *y; int i; VBranch *br; } VpappF;
static void vpapp_step(size_t off);
static void mpush_vpapp(Val *p, Val *r, Val *x, Val *y) { VpappF *f = mpush(sizeof *f, vpapp_step); f->p = p; f->r = r; f->x = x; f->y = y; }
#define F ((VpappF *)(mst.p + off))
static void vpapp_step(size_t off) {
    MSTART
    if (F->r->k != V_I) die("internal: path applied to a non-interval");
    MFORCE(F->p);
    if (iv_is_zero(F->r->iv)) MRET(F->x);
    if (iv_is_one(F->r->iv)) MRET(F->y);
    if (F->p->k == V_LAM) MTAIL(mpush_inst(&F->p->clo, F->r));
    if (F->p->k == V_SYS) {
        F->br = xalloc((F->p->nbr + 1) * sizeof(VBranch));
        for (F->i = 0; F->i < F->p->nbr; F->i++) {
            F->br[F->i].phi = F->p->br[F->i].phi;
            MCALL(mpush_vpapp(F->p->br[F->i].v, F->r, F->x, F->y));
            F->br[F->i].v = mret;
        }
        MRET(vsys(F->br, F->p->nbr));
    }
    { Val *p = F->p; Arg ar = {0}; ar.v = F->r; ar.papp = 1; ar.x = F->x; ar.y = F->y;
      meta_blocked = 1;
      if (p->k == V_NEU || p->k == V_DATA || p->k == V_CON) MRET(neu_app(p, ar));
      die("internal: path application to a non-path value"); }
    MFINISH
}
#undef F
Val *vpapp(Val *p, Val *r, Val *x, Val *y) { mpush_vpapp(p, r, x, y); return mrun(); }

typedef struct { MHdr h; Val *p; } PairSndF;
static void pair_snd_step(size_t off);
static void mpush_pair_snd(Val *p) { PairSndF *f = mpush(sizeof *f, pair_snd_step); f->p = p; }
#define F ((PairSndF *)(mst.p + off))
static void pair_snd_step(size_t off) {
    MSTART
    if (F->p->b) MRET(F->p->b);
    if (F->p->clo.fn) mret = F->p->clo.fn(F->p->clo.data, NULL);
    else MCALL(mpush_eval(F->p->clo.env, F->p->clo.t));
    F->p->b = mret;
    MRET(F->p->b);
    MFINISH
}
#undef F
Val *pair_snd(Val *p) { mpush_pair_snd(p); return mrun(); }

typedef struct { MHdr h; Val *p; int which, i; VBranch *br; } VprojF;
static void vproj_step(size_t off);
static void mpush_vproj(Val *p, int which) { VprojF *f = mpush(sizeof *f, vproj_step); f->p = p; f->which = which; }
#define F ((VprojF *)(mst.p + off))
static void vproj_step(size_t off) {
    MSTART
    /* A projection of a rigid definition application stays rigid (the H_DEF plan, one step further): the spine takes a
       proj entry, exactly as fst x on a variable does, conversion compares such spines by congruence, and force()
       unfolds through the projection where a canonical pair is needed (unfold_def replays proj entries). Forcing here
       instead evaluated the definition's whole body for every projection written in a TYPE - two copies of a 64-level
       loop, compared closure by closure (Bug_Eezott_ProjectionForcesDef_ExponentialConv). */
    MFMETA(F->p);
    { Val *r = F->p; if (r->k == V_NEU && r->h == H_DEF) { Arg ar = {0}; ar.proj = F->which; MRET(neu_app(r, ar)); } }
    MFORCE(F->p);
    if (F->p->k == V_PAIR) { if (F->which == 1) MRET(F->p->a); MTAIL(mpush_pair_snd(F->p)); }
    if (F->p->k == V_SYS) {
        F->br = xalloc((F->p->nbr + 1) * sizeof(VBranch));
        for (F->i = 0; F->i < F->p->nbr; F->i++) {
            F->br[F->i].phi = F->p->br[F->i].phi;
            MCALL(mpush_vproj(F->p->br[F->i].v, F->which));
            F->br[F->i].v = mret;
        }
        MRET(vsys(F->br, F->p->nbr));
    }
    { Arg ar = {0}; ar.proj = F->which;
      meta_blocked = 1;
      if (F->p->k == V_NEU) MRET(neu_app(F->p, ar));
      die("internal: projection from a non-pair value"); }
    MFINISH
}
#undef F
Val *vproj(Val *p, int which) { mpush_vproj(p, which); return mrun(); }
static Val *apply_arg(Val *f, Arg *a) { mpush_apply_arg(f, a); return mrun(); }
Val *vapply_arg(Val *f, Arg *a) { return apply_arg(f, a); }

/* ---- evaluation ----
   The term's own kinds: the ones that need no evaluation of subterms are values at once; the others hand the frame to
   a step of their kind (MBECOME), which evaluates the subterms left to right into v[] and then combines them. */
typedef struct { MHdr h; Env *env; Term *t; Val *v[4]; int i, j, k, n, cap, nf; VBranch *br; Face *fs; Env **cell; } EvalF;
static void eval_step(size_t off);
static void eval_sub_step(size_t off);
static void eval_let_step(size_t off);
static void eval_sys_step(size_t off);
static void eval_pair_step(size_t off);
static void mpush_eval(Env *env, Term *t) { EvalF *f = mpush(sizeof *f, eval_step); f->env = env; f->t = t; }
#define F ((EvalF *)(mst.p + off))
/* how many subterms a kind evaluates before combining (a, b, c, d in order); 0: not one of these kinds */
static int eval_nsub(Term *t) {
    switch (t->k) {
    case T_PI: case T_SIGMA: case T_INS: case T_FST: case T_SND: case T_INEG: return 1;
    case T_APP: case T_IAND: case T_IOR: case T_PARTIAL: return 2;
    case T_PATHP: case T_TRANSP: case T_SUB: case T_GLUE: case T_GLUEEL: return 3;
    case T_PAPP: case T_HCOMP: case T_OUTS: return 4;
    case T_UNGLUE: return 4;
    default: return 0;
    }
}
static Term *eval_sub(Term *t, int i) {
    if (t->k == T_UNGLUE) { Term *o[4] = { t->b, t->c, t->d, t->a }; return o[i]; }   /* vunglue's argument order */
    Term *o[4] = { t->a, t->b, t->c, t->d }; return o[i];
}
static void eval_step(size_t off) {
    Term *t = F->t; Env *env = F->env;
    switch (t->k) {
    case T_VAR: MRET(env_get(env, t->n));
    case T_U: { LVal l = t->a ? eval_level(env, t->a) : lv_const(t->n); MRET(t->pre ? vupre_l(l) : vu_l(l)); }
    case T_LEVEL: MRET(vlevel());
    case T_LZERO: case T_LSUC: case T_LMAX: case T_LMETA: MRET(vl(eval_level(env, t)));
    case T_LAM: { Val *v = mkval(V_LAM); v->name = t->name; v->irr = t->irr; v->isi = t->isi; v->imp = t->imp; v->clo.env = env; v->clo.t = t->a; MRET(v); }
    case T_DEF: {   /* rigid: a definition application (H_DEF), unfolded where a canonical form is needed */
        Val *v = mkval(V_NEU); v->h = H_DEF; v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); MRET(v);
    }
    case T_DATA: { Val *v = mkval(V_DATA); v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); MRET(v); }
    case T_CON: { Val *v = mkval(V_CON); v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); MRET(v); }
    case T_NUM: MRET(vnum(t->n, t->a ? eval_level(env, t->a) : lv_const(0), t->num));
    case T_ELIM: { Val *v = mkval(V_NEU); v->h = H_ELIM; v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); MRET(v); }
    case T_LVAL: MRET(vl(t->lvl));
    case T_META: { Meta *m = &tmetas[t->n]; if (m->sol) MRET(m->sol); Val *v = mkval(V_NEU); v->h = H_META; v->n = t->n; MRET(v); }
    case T_INTERVAL: MRET(vinterval());
    case T_I0: MRET(vi(iv_zero()));
    case T_I1: MRET(vi(iv_one()));
    case T_IRR: MRET(mkval(V_IRR));
    case T_LET: MBECOME(eval_let_step);
    case T_SYS: MBECOME(eval_sys_step);
    case T_PAIR: MBECOME(eval_pair_step);
    default:
        if (eval_nsub(t)) { F->n = eval_nsub(t); MBECOME(eval_sub_step); }
        MRET(NULL);
    }
}
static void eval_sub_step(size_t off) {
    MSTART
    for (F->i = 0; F->i < F->n; F->i++) {
        MCALL(mpush_eval(F->env, eval_sub(F->t, F->i)));
        F->v[F->i] = mret;
    }
    { Term *t = F->t; Val **v = F->v; Env *env = F->env;
      switch (t->k) {
      case T_PI: { Val *r = mkval(V_PI); r->name = t->name; r->irr = t->irr; r->isi = t->isi; r->imp = t->imp; r->dom = v[0]; r->clo.env = env; r->clo.t = t->b; MRET(r); }
      case T_SIGMA: { Val *r = mkval(V_SIGMA); r->name = t->name; r->irr = t->irr; r->dom = v[0]; r->clo.env = env; r->clo.t = t->b; MRET(r); }
      case T_INS: { Val *r = mkval(V_INS); r->a = v[0]; MRET(r); }
      case T_INEG: MRET(vi(iv_neg(v[0]->iv)));
      case T_IAND: MRET(vi(iv_and(v[0]->iv, v[1]->iv)));
      case T_IOR: MRET(vi(iv_or(v[0]->iv, v[1]->iv)));
      case T_PATHP: { Val *r = mkval(V_PATHP); r->a = v[0]; r->b = v[1]; r->c = v[2]; MRET(r); }
      case T_PARTIAL: { Val *r = mkval(V_PARTIAL); r->a = v[0]; r->b = v[1]; MRET(r); }
      case T_SUB: { Val *r = mkval(V_SUB); r->a = v[0]; r->b = v[1]; r->c = v[2]; MRET(r); }
      case T_TRANSP: MRET(vtransp(v[0], v[1], v[2]));
      case T_HCOMP: MRET(vhcomp(v[0], v[1], v[2], v[3]));
      case T_GLUE: { Val *g = vglue(v[0], v[1], v[2]); if (g->k == V_GLUE) g->lvl = t->d ? eval_level(env, t->d) : lv_const(t->n); MRET(g); }
      case T_GLUEEL: MRET(vglueel(v[0], v[1], v[2]));
      case T_UNGLUE: MRET(vunglue(v[0], v[1], v[2], v[3]));
      case T_OUTS: MRET(vouts(v[0], v[1], v[2], v[3]));
      case T_APP: { Val *f = v[0], *a = v[1]; int irr = t->irr; MTAIL(mpush_vapp(f, a, irr)); }
      case T_PAPP: { Val *p = v[0], *r = v[1], *x = v[2], *y = v[3]; MTAIL(mpush_vpapp(p, r, x, y)); }
      case T_FST: { Val *p = v[0]; MTAIL(mpush_vproj(p, 1)); }
      case T_SND: { Val *p = v[0]; MTAIL(mpush_vproj(p, 2)); }
      default: MRET(NULL);
      } }
    MFINISH
}
static void eval_let_step(size_t off) {
    MSTART
    MCALL(mpush_eval(F->env, F->t->b));
    { Env *e = env_push(F->env, mret); Term *body = F->t->c; MTAIL(mpush_eval(e, body)); }
    MFINISH
}
static void eval_pair_step(size_t off) {
    MSTART
    F->v[0] = mkval(V_PAIR); F->v[0]->irr = F->t->irr; F->v[0]->n = F->t->n;
    MCALL(mpush_eval(F->env, F->t->a));
    F->v[0]->a = mret;
    if (F->t->irr) { F->v[0]->b = NULL; F->v[0]->clo.env = F->env; F->v[0]->clo.t = F->t->b; MRET(F->v[0]); }   /* lazy: forced by snd only */
    MCALL(mpush_eval(F->env, F->t->b));
    F->v[0]->b = mret;
    MRET(F->v[0]);
    MFINISH
}
/* a system: each branch is evaluated under the restriction to its face (per conjunct): a branch is only meaningful there */
static void eval_sys_step(size_t off) {
    MSTART
    F->cap = 4; F->n = 0; F->br = xalloc(F->cap * sizeof(VBranch));
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        MCALL(mpush_eval(F->env, F->t->br[F->i].face));
        F->nf = iv_faces(mret->iv, &F->fs);
        for (F->j = 0; F->j < F->nf; F->j++) {
            if (F->n == F->cap) { F->cap *= 2; VBranch *b2 = xalloc(F->cap * sizeof(VBranch)); memcpy(b2, F->br, F->n * sizeof(VBranch)); F->br = b2; }
            F->cell = xalloc(sizeof *F->cell); *F->cell = F->env;
            for (F->k = 0; F->k < F->fs[F->j].n; F->k++)
                MCALL(mpush_subst_env(*F->cell, F->cell, F->fs[F->j].var[F->k], F->fs[F->j].val[F->k] ? iv_one() : iv_zero()));
            F->br[F->n].phi = vi(face_iv(&F->fs[F->j]));
            MCALL(mpush_eval(*F->cell, F->t->br[F->i].body));
            F->br[F->n].v = mret; F->n++;
        }
    }
    MRET(vsys(F->br, F->n));
    MFINISH
}
#undef F
Val *eval(Env *env, Term *t) { mpush_eval(env, t); return mrun(); }

/* ---- metas, forcing, unfolding (the machine's) ---- */
typedef struct { MHdr h; Val *v, *r; int i; } FmetaF;
static void fmeta_step(size_t off);
static void mpush_fmeta(Val *v) { FmetaF *f = mpush(sizeof *f, fmeta_step); f->v = v; }
#define F ((FmetaF *)(mst.p + off))
static void fmeta_step(size_t off) {
    MSTART
    while (meta_solved_head(F->v)) {
        F->r = tmetas[F->v->n].sol;
        for (F->i = 0; F->i < F->v->args.n; F->i++) { MCALL(mpush_apply_arg(F->r, &F->v->args.a[F->i])); F->r = mret; }
        F->v = F->r;
    }
    MRET(F->v);
    MFINISH
}
#undef F
Val *fmeta(Val *v) { if (!meta_solved_head(v)) return v; mpush_fmeta(v); return mrun(); }
/* a field resolved through solved metas, on the machine (field is an F-> lvalue) */

/* force: the canonical value - metas resolved, definition applications unfolded, deferred eliminations reduced. The
   literal tripwire counts the forces active (force_depth): a frame's, as it was a C call's. */
typedef struct { MHdr h; Val *v, *u; } ForceF;
static void force_step(size_t off);
static void mpush_force(Val *v) { ForceF *f = mpush(sizeof *f, force_step); f->v = v; }
#define F ((ForceF *)(mst.p + off))
static void force_step(size_t off) {
    MSTART
    force_depth++;
    MFMETA(F->v);
    for (;;) {
        /* a rigid definition application unfolds; one that unfolds to itself (a native's guard neutral: a power no limb
           list holds) is as canonical as it gets */
        if (F->v->k == V_NEU && F->v->h == H_DEF) {
            MCALL(mpush_unfold_def(F->v)); F->u = mret; MFMETA(F->u);
            if (F->u == F->v) break;
            F->v = F->u; continue;
        }
        /* a deferred elimination reduces; a stuck one comes back as itself, its flag dropped */
        if (F->v->k == V_NEU && F->v->h == H_ELIM && F->v->defer) {
            MCALL(mpush_elim_force(F->v)); F->u = mret; MFMETA(F->u);
            if (F->u == F->v) break;
            F->v = F->u; continue;
        }
        break;
    }
    force_depth--;
    MRET(F->v);
    MFINISH
}
#undef F
Val *force(Val *v) { if (!force_needed(v)) return v; mpush_force(v); return mrun(); }

/* def_at: a global's value at a level (a polymorphic definition's body instantiated once per level) */
typedef struct { MHdr h; int id, n; LVal L; LMemoList *ml; } DefAtF;
static void def_at_step(size_t off);
static void mpush_def_at(int id, LVal L) { DefAtF *f = mpush(sizeof *f, def_at_step); f->id = id; f->L = L; }
static LMemoList *def_memo; static int ndef_memo;
#define F ((DefAtF *)(mst.p + off))
static void def_at_step(size_t off) {
    MSTART
    { Def *d = &defs[F->id]; int n;
      if (!d->poly) MRET(d->vval);
      if (!lv_is_const(F->L, &n)) {
          F->ml = memo_for(&def_memo, &ndef_memo, F->id); Val *r = lmemo_get(F->ml, F->L);
          if (r) MRET(r);
          F->n = -1;
      } else {
          F->n = n;
          if (n >= d->nat) {
              int m = n + 4; Val **nv = xalloc(m * sizeof(Val *)), **nt = xalloc(m * sizeof(Val *));
              for (int i = 0; i < d->nat; i++) { nv[i] = d->vval_at[i]; nt[i] = d->vty_at[i]; }
              d->vval_at = nv; d->vty_at = nt; d->nat = m;
          }
          if (d->vval_at[n]) MRET(d->vval_at[n]);
      } }
    MCALL(mpush_eval(NULL, subst_hidden(defs[F->id].val, F->L)));
    if (F->n < 0) { lmemo_put(F->ml, F->L, mret); MRET(mret); }
    defs[F->id].vval_at[F->n] = mret;
    MRET(mret);
    MFINISH
}
#undef F
Val *def_at(int id, LVal L) { mpush_def_at(id, L); return mrun(); }

/* a rigid definition application to its value: the definition applied to its spine. The unfolding is a pure
   function of the value (definition id, level, spine), so it is computed once and kept in the value itself: a
   rigidity-preserving application is the shared cell, and every later force of the same spine hits it. This is the
   memoization pass - without it each re-application of a nested definition's spine redoes the whole body (cost
   compounding with nesting depth; Finding_Eezott_EvalNoSharing_2026_09_14). Guarded by the spine length (neu_app
   lengthens spines) and the metas version (a solved meta can unstick what the memo took as neutral). */
typedef struct { MHdr h; Val *v, *f; int save, i; } UnfoldF;
static void unfold_def_step(size_t off);
static void mpush_unfold_def(Val *v) { UnfoldF *f = mpush(sizeof *f, unfold_def_step); f->v = v; }
#define F ((UnfoldF *)(mst.p + off))
static void unfold_def_step(size_t off) {
    MSTART
    { static int seen; if (!seen) { seen = 1; if (getenv("EEZOTT_UNFOLD_COUNTS")) unf_count = rcalloc(65536, sizeof(long)); } }
    { Val *v = F->v; if (v->unf && v->unf_n == v->args.n && (v->unf_mv == metas_version || v->unf_stable)) MRET(v->unf); }
    F->save = meta_blocked; meta_blocked = 0;
    if (unf_count) unf_count[F->v->n]++;   /* diagnostic: body evaluations per definition (EEZOTT_UNFOLD_COUNTS) */
    if (F->v->par && F->v->par->k == V_NEU && F->v->par->h == H_DEF && F->v->par->n == F->v->n && F->v->par->args.n + 1 == F->v->args.n) {
        /* incremental along the spine: the parent's unfolding (memoised there), then the one entry this neutral adds.
           Without this every projection or application written on a rigid definition re-evaluated its whole body. */
        MCALL(mpush_unfold_def(F->v->par)); F->f = mret;
        MCALL(mpush_apply_arg(F->f, &F->v->args.a[F->v->args.n - 1])); F->f = mret;
    } else {
        MCALL(mpush_def_at(F->v->n, F->v->lvl)); F->f = mret;
        for (F->i = 0; F->i < F->v->args.n; F->i++) { MCALL(mpush_apply_arg(F->f, &F->v->args.a[F->i])); F->f = mret; }
    }
    { Val *v = F->v; v->unf = F->f; v->unf_n = v->args.n; v->unf_mv = metas_version; v->unf_stable = !meta_blocked; }
    meta_blocked |= F->save;
    MRET(F->f);
    MFINISH
}
#undef F
Val *unfold_def(Val *v) { mpush_unfold_def(v); return mrun(); }

/* ---- eliminations (the machine's) ---- */
static void mpush_elim_reduce(int data, VList *args);
static void mpush_elim_apply_list(int data, VList args);
/* A saturated elimination is reduced on demand, as a rigid definition application is unfolded on demand: the value is
   the shared cell and its reduction is kept in it (unf), guarded as unfold_def's memo is. So an induction hypothesis
   is computed only where the method forces it, the branches of a decision only where the decision selects them, and
   a fold over a literal walks only as far as something forces (S2: what the chunk rule approximated by refusing).
   A stuck elimination (its target not canonical) comes back as itself with the flag dropped: the neutral it is. */
typedef struct { MHdr h; Val *v, *r; int save; } EforceF;
static void elim_force_step(size_t off);
static void mpush_elim_force(Val *v) { EforceF *f = mpush(sizeof *f, elim_force_step); f->v = v; }
#define F ((EforceF *)(mst.p + off))
static void elim_force_step(size_t off) {
    MSTART
    { Val *v = F->v;
      if (!v->defer) MRET(v);
      if (v->unf && v->unf_n == v->args.n && (v->unf_mv == metas_version || v->unf_stable)) MRET(v->unf); }
    F->save = meta_blocked; meta_blocked = 0;
    { Data *D = &datas[F->v->n];
      int arity = D->nparams + D->nblock + block_ncons(F->v->n) + D->nidx + 1;
      if (F->v->args.n > arity) goto applied; }
    elim_lvl = F->v->lvl;
    MCALL(mpush_elim_reduce(F->v->n, &F->v->args)); F->r = mret;
    if (!F->r) F->r = elim_hcomp(F->v->n, &F->v->args);
    if (!F->r) { F->v->defer = 0; meta_blocked |= F->save; MRET(F->v); }
    goto done;
applied:   /* an application of the elimination's result: the parent's reduction, then this entry */
    MCALL(mpush_elim_force(F->v->par)); F->r = mret;
    if (F->r == F->v->par) { F->v->defer = 0; meta_blocked |= F->save; MRET(F->v); }
    MCALL(mpush_apply_arg(F->r, &F->v->args.a[F->v->args.n - 1])); F->r = mret;
done:
    { Val *v = F->v; v->unf = F->r; v->unf_n = v->args.n; v->unf_mv = metas_version; v->unf_stable = !meta_blocked; }
    meta_blocked |= F->save;
    MRET(F->r);
    MFINISH
}
#undef F
Val *elim_force(Val *v) { if (!v->defer) return v; mpush_elim_force(v); return mrun(); }

typedef struct { MHdr h; int data, i; VList args; Val *r; } EapplyF;
static void elim_apply_list_step(size_t off);
static void mpush_elim_apply_list(int data, VList args) { EapplyF *f = mpush(sizeof *f, elim_apply_list_step); f->data = data; f->args = args; }
#define F ((EapplyF *)(mst.p + off))
static void elim_apply_list_step(size_t off) {
    MSTART
    F->r = mkval(V_NEU); F->r->h = H_ELIM; F->r->n = F->data; F->r->lvl = elim_lvl;
    for (F->i = 0; F->i < F->args.n; F->i++) { MCALL(mpush_vapp(F->r, F->args.a[F->i].v, F->args.a[F->i].irr)); F->r = mret; }
    MRET(F->r);
    MFINISH
}
#undef F
static Val *elim_apply_list(int data, VList *args) { mpush_elim_apply_list(data, *args); return mrun(); }

/* the motive of member `data` applied to the indices and, where an index ranges over a member, to its image: that member's
   elimination of it with the same prefix (M11b) */
typedef struct { MHdr h; int data, j; VList pre; Val **idx; Val *P; } MotiveF;
static void motive_applied_step(size_t off);
static void mpush_motive_applied(int data, VList pre, Val **idx) { MotiveF *f = mpush(sizeof *f, motive_applied_step); f->data = data; f->pre = pre; f->idx = idx; }
#define F ((MotiveF *)(mst.p + off))
static void motive_applied_step(size_t off) {
    MSTART
    { Data *D = &datas[F->data]; F->P = F->pre.a[D->nparams + D->bpos].v; }
    for (F->j = 0; F->j < datas[F->data].nidx; F->j++) {
        MCALL(mpush_vapp(F->P, F->idx[F->j], 1)); F->P = mret;
        if (datas[F->data].idxrec[F->j] >= 0) {
            { Data *D = &datas[F->data]; int np = D->nparams, nb = D->nblock, K = block_ncons(F->data);
              VList a2 = {0}; for (int i = 0; i < np + nb + K; i++) vl_push(&a2, F->pre.a[i].v, prefix_irr(F->data, i));
              vl_push(&a2, F->idx[F->j], 0);
              MCALL(mpush_elim_apply_list(D->idxrec[F->j], a2)); }
            MCALL(mpush_vapp(F->P, mret, 0)); F->P = mret;
        }
    }
    MRET(F->P);
    MFINISH
}
#undef F
static Val *motive_applied(int data, VList *pre, Val **idx) { mpush_motive_applied(data, *pre, idx); return mrun(); }

/* The literal-elimination tripwire (see below) and iota. */
typedef struct { MHdr h; int data; VList *args; Val *target; } EreduceF;
typedef struct { MHdr h; int data; VList *args; Data *D; int np, nb, K, j, q, end; Val *target; Con *c; Val *res;
                 Native *ih; Env *e; VList a2; Val *ends[2]; Val *bsys, *img, *P; } ErgoF;
static void elim_reduce_step(size_t off);
static void elim_reduce_go_step(size_t off);
static void mpush_elim_reduce(int data, VList *args) { EreduceF *f = mpush(sizeof *f, elim_reduce_step); f->data = data; f->args = args; }
static void mpush_elim_reduce_go(int data, VList *args) { ErgoF *f = mpush(sizeof *f, elim_reduce_go_step); f->data = data; f->args = args; }
#define F ((EreduceF *)(mst.p + off))
static void elim_reduce_step(size_t off) {
    MSTART
    F->target = F->args->a[F->args->n - 1].v;
    MFORCE(F->target);
    if (F->target->k != V_NUM) MTAIL(mpush_elim_reduce_go(F->data, F->args));
    { Val *target = F->target; int data = F->data; VList *args = F->args;
      int bits = bn_bitlen(target->num);
      /* a machine-sized literal walked past 64 levels, or ANY literal nested past 4096: the second rule is the
         backstop for walks on literals below the word bounds, which the first rule cannot see (closed computations
         nest legitimately - the power's bit loop is 64 levels per limb - so the floor is generous). The nesting is
         the eliminations' or the forces': a step whose method returns a rigid native over its hypothesis (mul 3 ih)
         walks when the native forces it, each step inside the last native's force, and elim_reduce itself returns
         every time - so the forces are counted too (S2). Both counts are frames on the machine now, as they were C
         calls. */
      int nest = elim_num_depth > force_depth ? elim_num_depth : force_depth;
      if ((bits > 40 && nest > 64) || nest > 4096) {
          char *dec = bn_to_dec(target->num);   /* name the literal itself: the bits alone do not say which bound was walked */
          if (strlen(dec) > 40) { dec[40] = 0; }
          if (getenv("EEZOTT_TRIPWIRE_METHODS")) {   /* the nesting chain's outermost levels, then the eliminator's methods */
              for (int i = 0; i < 3 && i < elim_num_depth; i++) fprintf(stderr, "  level %d: elim %s on %s\n", i, datas[elim_trace[i].data].name, elim_trace[i].lit);
              fprintf(stderr, "  last native fallback: code %d, arg1 = %s; arg2 = %s\n", last_fallback_code, last_fallback[0], last_fallback[1]);
              Data *D = &datas[data]; int np = D->nparams, nb = D->nblock;
              for (int i = np + nb; i < args->n - 1; i++) {
                  Val *m = args->a[i].v;
                  fprintf(stderr, "  method %d: ", i - np - nb);
                  if (m->k == V_LAM && m->clo.t) term_heads(stderr, m->clo.t, 0); else fprintf(stderr, "(kind %d)", m->k);
                  fputc('\n', stderr);
              }
          }
          resource_die("elimination of %s recursed %d deep on the literal %s in %s: the induction hypothesis is used, so this is work proportional to the literal",
                       datas[data].name, nest, dec, cur_decl_name ? cur_decl_name : "the top level");
      }
      if (elim_num_depth < 64) { char *dd = bn_to_dec(target->num); elim_trace[elim_num_depth].data = data; snprintf(elim_trace[elim_num_depth].lit, 16, "%s", dd); free(dd); } }
    elim_num_depth++;
    MCALL(mpush_elim_reduce_go(F->data, F->args));
    elim_num_depth--;
    MRET(mret);
    MFINISH
}
#undef F

#define F ((ErgoF *)(mst.p + off))
static void elim_reduce_go_step(size_t off) {
    MSTART
    F->D = data_at(F->data, elim_lvl); elim_data_cur = F->data;
    F->np = F->D->nparams; F->nb = F->D->nblock; F->K = block_ncons(F->data);
    F->target = F->args->a[F->args->n - 1].v;
    MFORCE(F->target);   /* a rigid definition application unfolds for the elimination */
    if (F->target->k == V_NUM) F->target = num_view(F->target);   /* a literal eliminates as one constructor */
    if (F->target->k != V_CON) { meta_blocked = 1; MRET(NULL); }
    F->c = con_at(F->target->n, F->target->lvl);
    if (F->c->data != F->data || F->target->args.n != F->np + F->c->nargs + F->c->nint) { meta_blocked = 1; MRET(NULL); }
    F->res = F->args->a[F->np + F->nb + F->c->bord].v;
    for (F->j = 0; F->j < F->c->nargs; F->j++) { MCALL(mpush_vapp(F->res, F->target->args.a[F->np + F->j].v, F->c->args[F->j].irr)); F->res = mret; }
    for (F->j = 0; F->j < F->c->nargs; F->j++) {
        if (F->c->args[F->j].isrecpath) {   /* the induction hypothesis over a path argument is the dependent path  k. elim .. idx (p k) */
            F->ih = xalloc(sizeof *F->ih); F->ih->code = N_ELIM_PATH_IH; F->ih->i1 = F->c->args[F->j].rec;
            for (int i = 0; i < F->np + F->nb + F->K; i++) vl_push(&F->ih->cap, F->args->a[i].v, prefix_irr(F->data, i));
            F->e = NULL; for (int i = 0; i < F->np + F->j; i++) F->e = env_push(F->e, F->target->args.a[i].v);
            for (F->q = 0; F->q < F->c->args[F->j].nidx; F->q++) { MCALL(mpush_eval(F->e, F->c->args[F->j].idx[F->q])); vl_push(&F->ih->cap, mret, 1); }
            vl_push(&F->ih->cap, F->target->args.a[F->np + F->j].v, 0);
            MCALL(mpush_eval(F->e, F->c->args[F->j].px)); vl_push(&F->ih->cap, mret, 0);
            MCALL(mpush_eval(F->e, F->c->args[F->j].py)); vl_push(&F->ih->cap, mret, 0);
            { Val *ihv = mkval(V_LAM); ihv->clo.fn = nfn; ihv->clo.data = F->ih; ihv->name = "k"; ihv->isi = 1;
              MCALL(mpush_vapp(F->res, ihv, 0)); }
            F->res = mret;
            continue;
        }
        if (!F->c->args[F->j].isrec) continue;
        /* a method that does not mention its induction hypothesis does not get one at all: a case analysis on a literal
           (isZero, pred, if01 ..) then never builds the recursive elimination (M16a). One that does gets it deferred:
           elim_apply_list ends in a saturated elimination, which vapp leaves unreduced until something forces it. */
        if (F->c->args[F->j].npi == 0 && F->res->k == V_LAM && !F->res->clo.fn && !term_mentions_var(F->res->clo.t, 0)) {
            MCALL(mpush_vapp(F->res, F->target->args.a[F->np + F->j].v, 0)); F->res = mret; continue;
        }
        F->ih = xalloc(sizeof *F->ih); F->ih->code = N_IH; F->ih->i1 = F->c->args[F->j].rec; F->ih->i2 = F->target->n; F->ih->i3 = F->j; F->ih->l = elim_lvl;
        for (int i = 0; i < F->np + F->nb + F->K; i++) vl_push(&F->ih->cap, F->args->a[i].v, 0);
        for (int i = 0; i < F->np; i++) vl_push(&F->ih->cap, F->target->args.a[i].v, 0);
        for (int i = 0; i < F->j; i++) vl_push(&F->ih->cap, F->target->args.a[F->np + i].v, 0);
        vl_push(&F->ih->cap, F->target->args.a[F->np + F->j].v, 0);
        if (F->c->args[F->j].npi == 0) {
            F->e = NULL; for (int i = 0; i < F->np + F->j; i++) F->e = env_push(F->e, F->ih->cap.a[F->np + F->nb + F->K + i].v);
            F->a2 = (VList){0};
            for (int i = 0; i < F->np + F->nb + F->K; i++) vl_push(&F->a2, F->args->a[i].v, prefix_irr(F->data, i));
            for (F->q = 0; F->q < F->c->args[F->j].nidx; F->q++) { MCALL(mpush_eval(F->e, F->c->args[F->j].idx[F->q])); vl_push(&F->a2, mret, 1); }
            vl_push(&F->a2, F->target->args.a[F->np + F->j].v, 0);
            MCALL(mpush_elim_apply_list(F->c->args[F->j].rec, F->a2));
        } else { Val *ihv = mkval(V_LAM); ihv->clo.fn = nfn; ihv->clo.data = F->ih; ihv->name = "y"; mret = ihv; }
        MCALL(mpush_vapp(F->res, mret, 0)); F->res = mret;
    }
    if (F->c->nint == 0) MRET(F->res);
    /* a path constructor: the method is a cube with the prescribed boundary */
    if (F->c->pathmethod) {   /* PathP (i. P (c a i)) (elim .. b0) (elim .. b1) */
        for (F->end = 0; F->end < 2; F->end++) {
            { Env *e0 = NULL;
              for (int i = 0; i < F->np + F->c->nargs; i++) e0 = env_push(e0, F->target->args.a[i].v);
              e0 = env_push(e0, vi(F->end ? iv_one() : iv_zero()));
              MCALL(mpush_eval(e0, F->c->boundary)); }
            { Val *b = mret;
              if (b->k == V_SYS) die("internal: boundary of %s not total at an endpoint", F->c->name);
              VList a2 = vl_copy(F->args); a2.n = F->np + F->nb + F->K + F->D->nidx;   /* the boundary lives at the target's indices */
              vl_push(&a2, b, 0);
              MCALL(mpush_elim_apply_list(F->data, a2)); }
            F->ends[F->end] = mret;
        }
        { Val *res = F->res, *r = F->target->args.a[F->np + F->c->nargs].v, *e0 = F->ends[0], *e1 = F->ends[1];
          MTAIL(mpush_vpapp(res, r, e0, e1)); }
    }
    /* (is : I) -> Sub (P (c a is)) phi [faces -> elim .. boundary] */
    for (F->q = 0; F->q < F->c->nint; F->q++) { MCALL(mpush_vapp(F->res, F->target->args.a[F->np + F->c->nargs + F->q].v, 0)); F->res = mret; }
    if (!F->c->boundary) MRET(F->res);
    { Env *env = NULL;
      for (int i = 0; i < F->target->args.n; i++) env = env_push(env, F->target->args.a[i].v);
      MCALL(mpush_eval(env, F->c->boundary)); }
    F->bsys = mret;
    { VList base = vl_copy(F->args); base.n = F->np + F->nb + F->K + F->D->nidx;
      VList *bp = xalloc(sizeof *bp); *bp = base;
      F->img = vsys_map(F->bsys, elim_of_branch, bp); }
    { Val **iv = xalloc((F->D->nidx + 1) * sizeof(Val *));
      for (int j = 0; j < F->D->nidx; j++) iv[j] = F->args->a[F->np + F->nb + F->K + j].v;
      MCALL(mpush_motive_applied(F->data, *F->args, iv)); }
    F->P = mret;
    MCALL(mpush_vapp(F->P, F->target, 0));
    { IVal phi = iv_zero();
      if (F->bsys->k == V_SYS) { for (int i = 0; i < F->bsys->nbr; i++) phi = iv_or(phi, F->bsys->br[i].phi->iv); } else phi = iv_one();
      MRET(vouts(mret, vi(phi), F->img, F->res)); }
    MFINISH
}
#undef F

/* ---- induction hypotheses (native closure N_IH) ----
   cap = base (params, motive, methods), tele (params, previous args), ys, aj; i1=data i2=con i3=j; ys count = cap.n - nb - nt - 1 */
typedef struct { MHdr h; Native *c, *d; int nb, nt, ny, i; Env *e; VList args; Val *t; } IhF;
static void ih_apply_step(size_t off);
static void mpush_ih_apply(Native *c, Val *y) {
    IhF *f = mpush(sizeof *f, ih_apply_step); f->c = c;
    Native *d = xalloc(sizeof *d); *d = *c; d->cap = vl_copy(&c->cap);
    /* insert y before the trailing aj */
    Arg aj = d->cap.a[d->cap.n - 1]; d->cap.n--; vl_push(&d->cap, y, 0); vl_push_arg(&d->cap, aj);
    f->d = d;
}
#define F ((IhF *)(mst.p + off))
static void ih_apply_step(size_t off) {
    MSTART
    F->nb = datas[F->c->i1].nparams + datas[F->c->i1].nblock + block_ncons(F->c->i1);
    F->nt = datas[F->c->i1].nparams + F->c->i3;
    F->ny = F->d->cap.n - F->nb - F->nt - 1;
    { ConArg *ca = &con_at(F->c->i2, F->c->l)->args[F->c->i3];
      if (F->ny < ca->npi) { Val *v = mkval(V_LAM); v->clo.fn = nfn; v->clo.data = F->d; v->name = "y"; MRET(v); } }
    F->e = NULL; for (int i = 0; i < F->nt; i++) F->e = env_push(F->e, F->d->cap.a[F->nb + i].v);
    for (int i = 0; i < F->ny; i++) F->e = env_push(F->e, F->d->cap.a[F->nb + F->nt + i].v);
    F->args = (VList){0};
    for (int i = 0; i < F->nb; i++) vl_push(&F->args, F->d->cap.a[i].v, prefix_irr(F->c->i1, i));
    for (F->i = 0; F->i < con_at(F->c->i2, F->c->l)->args[F->c->i3].nidx; F->i++) {
        MCALL(mpush_eval(F->e, con_at(F->c->i2, F->c->l)->args[F->c->i3].idx[F->i]));
        vl_push(&F->args, mret, 1);
    }
    F->t = F->d->cap.a[F->d->cap.n - 1].v;
    for (F->i = 0; F->i < F->ny; F->i++) { MCALL(mpush_vapp(F->t, F->d->cap.a[F->nb + F->nt + F->i].v, 0)); F->t = mret; }
    vl_push(&F->args, F->t, 0);
    { int data = F->c->i1; VList a = F->args; MTAIL(mpush_elim_apply_list(data, a)); }
    MFINISH
}
#undef F
static Val *ih_apply(Native *c, Val *y) { mpush_ih_apply(c, y); return mrun(); }

/* ---- restriction to a face (the machine's) ----
   A value with an interval variable substituted, rebuilt bottom up by frames: its parts in the order the recursion
   took them, closures' captured values and environments included (an environment is rebuilt entry by entry, in
   order). A closure or environment frame writes into a destination on the heap (the new value's own field), never
   into the machine's stack. */
static void mpush_subst(Val *v, int lv, IVal s);
typedef struct { MHdr h; Env *e, **dst; int lv; IVal s; } SubstEnvF;
static void subst_env_step(size_t off);
static void mpush_subst_env(Env *e, Env **dst, int lv, IVal s) { SubstEnvF *f = mpush(sizeof *f, subst_env_step); f->e = e; f->dst = dst; f->lv = lv; f->s = s; }
#define F ((SubstEnvF *)(mst.p + off))
static void subst_env_step(size_t off) {
    MSTART
    *F->dst = NULL;
    while (F->e) {
        { Env *n = xalloc(sizeof *n); *F->dst = n; F->dst = &n->next; n->next = NULL; }
        MCALL(mpush_subst(F->e->v, F->lv, F->s));
        { Env *n = (Env *)((char *)F->dst - offsetof(Env, next)); n->v = mret; }
        F->e = F->e->next;
    }
    MRET(NULL);
    MFINISH
}
#undef F

typedef struct { MHdr h; Clo *dst; const Clo *src; int lv; IVal s; int i, n; void *data; } SubstCloF;
static void subst_clo_step(size_t off);
static void mpush_subst_clo(Clo *dst, const Clo *src, int lv, IVal s) { SubstCloF *f = mpush(sizeof *f, subst_clo_step); f->dst = dst; f->src = src; f->lv = lv; f->s = s; }
#define F ((SubstCloF *)(mst.p + off))
static void subst_clo_step(size_t off) {
    MSTART
    *F->dst = *F->src;
    F->dst->iarg = NULL; F->dst->ires = NULL; F->dst->imv = 0;   /* the substitution changes what the closure computes */
    if (!F->src->fn) { MCALL(mpush_subst_env(F->src->env, &F->dst->env, F->lv, F->s)); MRET(NULL); }
    if (F->src->fn == natfn) {
        { NatNative *nn = F->src->data, *m = xalloc(sizeof *m); *m = *nn; F->data = m; }
        MCALL(mpush_subst(((NatNative *)F->src->data)->fallback, F->lv, F->s)); ((NatNative *)F->data)->fallback = mret;
        if (((NatNative *)F->src->data)->arg1) { MCALL(mpush_subst(((NatNative *)F->src->data)->arg1, F->lv, F->s)); ((NatNative *)F->data)->arg1 = mret; }
        F->dst->data = F->data; MRET(NULL);
    }
    if (F->src->fn != nfn) {   /* closures built by the Kan rules with plain structs of values: a Val* array of known length */
        { Caps *c = F->src->data, *r = xalloc(sizeof *r); *r = *c; F->data = r; F->n = c->n; }
        for (F->i = 0; F->i < F->n; F->i++) { MCALL(mpush_subst(((Caps *)F->src->data)->v[F->i], F->lv, F->s)); ((Caps *)F->data)->v[F->i] = mret; }
        F->dst->data = F->data; MRET(NULL);
    }
    { Native *nt = F->src->data, *nn = xalloc(sizeof *nn); *nn = *nt; nn->cap = (VList){0}; F->data = nn; }
    for (F->i = 0; F->i < ((Native *)F->src->data)->cap.n; F->i++) {
        MCALL(mpush_subst(((Native *)F->src->data)->cap.a[F->i].v, F->lv, F->s));
        vl_push(&((Native *)F->data)->cap, mret, ((Native *)F->src->data)->cap.a[F->i].irr);
    }
    F->dst->data = F->data;
    MRET(NULL);
    MFINISH
}
#undef F

typedef struct { MHdr h; Val *v, *r, *head; int lv; IVal s; int i; Val *x[4]; VBranch *br; Arg a; } SubstF;
static void subst_step(size_t off);
static void subst_clo_kind_step(size_t off);
static void subst_parts_step(size_t off);
static void subst_sys_step(size_t off);
static void subst_args_step(size_t off);
static void mpush_subst(Val *v, int lv, IVal s) { SubstF *f = mpush(sizeof *f, subst_step); f->v = v; f->lv = lv; f->s = s; }
#define F ((SubstF *)(mst.p + off))
/* the parts a kind substitutes before rebuilding (a, b, c, then dom), and whether it has any */
static int subst_nparts(Val *v) {
    switch (v->k) {
    case V_PATHP: case V_SUB: case V_GLUE: case V_GLUEEL: return 3;
    case V_PARTIAL: return 2;
    case V_INS: return 1;
    case V_NEU: return v->h == H_TRANSP ? 3 : (v->h == H_HCOMP || v->h == H_OUTS || v->h == H_UNGLUE) ? 4 : 0;
    default: return 0;
    }
}
static Val *subst_part(Val *v, int i) { Val *o[4] = { v->a, v->b, v->c, v->dom }; return o[i]; }
static void subst_step(size_t off) {
    Val *v = F->v;
    switch (v->k) {
    case V_U: case V_INTERVAL: case V_L: case V_LEVEL: case V_IRR: case V_NUM: MRET(v);   /* a number is closed */
    case V_I: MRET(vi(iv_subst(v->iv, F->lv, F->s)));
    case V_LAM: case V_PI: case V_SIGMA: case V_PAIR: MBECOME(subst_clo_kind_step);
    case V_SYS: MBECOME(subst_sys_step);
    case V_DATA: case V_CON: MBECOME(subst_args_step);
    case V_NEU:
        switch (v->h) {
        case H_VAR: F->head = vvar(v->n); MBECOME(subst_args_step);
        case H_ELIM: F->head = mkval(V_NEU); F->head->h = H_ELIM; F->head->n = v->n; F->head->lvl = v->lvl; MBECOME(subst_args_step);
        case H_DEF: F->head = mkval(V_NEU); F->head->h = H_DEF; F->head->n = v->n; F->head->lvl = v->lvl; MBECOME(subst_args_step);
        case H_META: MBECOME(subst_args_step);
        case H_TRANSP: case H_HCOMP: case H_OUTS: case H_UNGLUE: MBECOME(subst_parts_step);
        default: die("internal: unknown neutral head");
        }
    default: MBECOME(subst_parts_step);
    }
}
static void subst_clo_kind_step(size_t off) {
    MSTART
    F->r = mkval(F->v->k);
    if (F->v->k == V_PAIR) { F->r->irr = F->v->irr; F->r->n = F->v->n; } else *F->r = *F->v;
    if (F->v->k == V_PI || F->v->k == V_SIGMA) { MCALL(mpush_subst(F->v->dom, F->lv, F->s)); F->r->dom = mret; }
    if (F->v->k == V_PAIR) {
        MCALL(mpush_subst(F->v->a, F->lv, F->s)); F->r->a = mret;
        if (F->v->b) { MCALL(mpush_subst(F->v->b, F->lv, F->s)); F->r->b = mret; MRET(F->r); }
        F->r->b = NULL;
    }
    MCALL(mpush_subst_clo(&F->r->clo, &F->v->clo, F->lv, F->s));
    MRET(F->r);
    MFINISH
}
static void subst_parts_step(size_t off) {
    MSTART
    for (F->i = 0; F->i < subst_nparts(F->v); F->i++) { MCALL(mpush_subst(subst_part(F->v, F->i), F->lv, F->s)); F->x[F->i] = mret; }
    { Val *v = F->v, **x = F->x;
      switch (v->k) {
      case V_PATHP: { Val *r = mkval(V_PATHP); r->a = x[0]; r->b = x[1]; r->c = x[2]; MRET(r); }
      case V_PARTIAL: { Val *r = mkval(V_PARTIAL); r->a = x[0]; r->b = x[1]; MRET(r); }
      case V_SUB: { Val *r = mkval(V_SUB); r->a = x[0]; r->b = x[1]; r->c = x[2]; MRET(r); }
      case V_INS: { Val *r = mkval(V_INS); r->a = x[0]; MRET(r); }
      case V_GLUE: { Val *g = vglue(x[0], x[1], x[2]); if (g->k == V_GLUE) g->lvl = v->lvl; MRET(g); }
      case V_GLUEEL: MRET(vglueel(x[0], x[1], x[2]));
      case V_NEU:
          if (v->h == H_TRANSP) F->head = vtransp(x[0], x[1], x[2]);
          else if (v->h == H_HCOMP) F->head = vhcomp(x[0], x[1], x[2], x[3]);
          else if (v->h == H_OUTS) F->head = vouts(x[0], x[1], x[2], x[3]);
          else F->head = vunglue(x[0], x[1], x[2], x[3]);
          MBECOME(subst_args_step);
      default: MRET(v);
      } }
    MFINISH
}
static void subst_sys_step(size_t off) {
    MSTART
    F->br = xalloc((F->v->nbr + 1) * sizeof(VBranch));
    for (F->i = 0; F->i < F->v->nbr; F->i++) {
        MCALL(mpush_subst(F->v->br[F->i].phi, F->lv, F->s)); F->br[F->i].phi = mret;
        MCALL(mpush_subst(F->v->br[F->i].v, F->lv, F->s)); F->br[F->i].v = mret;
    }
    MRET(vsys(F->br, F->v->nbr));
    MFINISH
}
/* a spine: each argument substituted, then applied to the head built so far (a data type or constructor keeps its
   arguments as a list; a meta is resolved first, and substituted in its solution if it has one) */
static void subst_args_step(size_t off) {
    MSTART
    if (F->v->k == V_NEU && F->v->h == H_META) {
        F->r = F->v; MFORCE(F->r);
        if (F->r != F->v) { Val *fv = F->r; int lv = F->lv; IVal s = F->s; MTAIL(mpush_subst(fv, lv, s)); }
        F->head = mkval(V_NEU); F->head->h = H_META; F->head->n = F->v->n;
    }
    if (F->v->k == V_DATA || F->v->k == V_CON) { F->head = mkval(F->v->k); F->head->n = F->v->n; F->head->lvl = F->v->lvl; F->head->args = (VList){0}; }
    for (F->i = 0; F->i < F->v->args.n; F->i++) {
        F->a = F->v->args.a[F->i];
        if (F->a.v) { MCALL(mpush_subst(F->a.v, F->lv, F->s)); F->a.v = mret; }
        if (F->a.papp) { MCALL(mpush_subst(F->a.x, F->lv, F->s)); F->a.x = mret; MCALL(mpush_subst(F->a.y, F->lv, F->s)); F->a.y = mret; }
        if (F->v->k == V_DATA) { F->a.irr = 0; vl_push_arg(&F->head->args, F->a); continue; }
        if (F->v->k == V_CON) { F->a.irr = 0; MCALL(mpush_vapp(F->head, F->a.v, 0)); F->head = mret; continue; }
        { Arg *ap = xalloc(sizeof *ap); *ap = F->a; MCALL(mpush_apply_arg(F->head, ap)); }
        F->head = mret;
    }
    MRET(F->head);
    MFINISH
}
#undef F
Val *subst_val(Val *v, int lv, IVal s) { mpush_subst(v, lv, s); return mrun(); }

typedef struct { MHdr h; Val *v; const Face *f; int i; } RestrictF;
static void restrict_step(size_t off);
static void mpush_restrict(Val *v, const Face *f) { RestrictF *x = mpush(sizeof *x, restrict_step); x->v = v; x->f = f; }
#define F ((RestrictF *)(mst.p + off))
static void restrict_step(size_t off) {
    MSTART
    if (F->f) for (F->i = 0; F->i < F->f->n; F->i++) {
        MCALL(mpush_subst(F->v, F->f->var[F->i], F->f->val[F->i] ? iv_one() : iv_zero()));
        F->v = mret;
    }
    MRET(F->v);
    MFINISH
}
#undef F
Val *restrict_val(Val *v, const Face *f) { if (!f) return v; mpush_restrict(v, f); return mrun(); }

/* ---- Kan operations ---- */
static Val *neu_transp(Val *line, Val *phi, Val *u0) { Val *v = mkval(V_NEU); v->h = H_TRANSP; v->a = line; v->b = phi; v->c = u0; return v; }
static Val *neu_hcomp(Val *A, Val *phi, Val *u, Val *u0) { Val *v = mkval(V_NEU); v->h = H_HCOMP; v->a = A; v->b = phi; v->c = u; v->dom = u0; return v; }
static Val *ior(Val *a, Val *b) { return vi(iv_or(a->iv, b->iv)); }
static Val *iand(Val *a, Val *b) { return vi(iv_and(a->iv, b->iv)); }
static Val *ineg(Val *a) { return vi(iv_neg(a->iv)); }
static Val *ione(void) { return vi(iv_one()); }
static Val *izero(void) { return vi(iv_zero()); }
#define CAP(nt, i) ((nt)->cap.a[i].v)

/* forward transport: fwd line r u = transp (λi. line (i ∨ r)) r u */
static Val *vfwd(Val *line, Val *r, Val *u) { return vtransp(vnative(N_LINE_IOR, 0, 0, 0, 2, line, r), r, u); }
/* heterogeneous composition: comp line phi u u0 = hcomp (line i1) phi (λi. fwd line i (u i)) (fwd line i0 u0) */
static Val *vcomp(Val *line, Val *phi, Val *u, Val *u0) {
    return vhcomp(vapp(line, ione(), 0), phi, vnative(N_FWD_SIDES, 0, 0, 0, 2, line, u), vfwd(line, izero(), u0));
}
/* fillers */
static Val *vtfill(Val *line, Val *phi, Val *u0) { return vnative(N_TFILL, 0, 0, 0, 3, line, phi, u0); }     /* λi. transp (λj. line (i∧j)) (φ ∨ ~i) u0 */
static Val *vfill(Val *line, Val *phi, Val *u, Val *u0) { return vnative(N_FILL, 0, 0, 0, 4, line, phi, u, u0); } /* λi. comp (λj. line (i∧j)) (φ ∨ ~i) [..] u0 */

static Val *transp_branch(Val *b, void *data) { Native *nt = data; return vtransp(nt->cap.a[0].v, nt->cap.a[1].v, b); }
static Val *proj_arg(Val *v, void *data) { int k = *(int *)data; v = force(v); if (k < 0) return vproj(v, -k); if (v->k == V_NUM) v = num_view(v); if (v->k != V_CON && v->k != V_DATA) die("internal: projecting a non-constructor"); return v->args.a[k].v; }

/* Every native closure application is memoized the same way - a pure step, keyed on the argument value, tagged by the
   metas generation. An eliminator's induction hypothesis applied to the same value again is the same value, and branch
   bodies do apply the same closure to the same value repeatedly (baddGo's column uses its IH three times). */
static Val *native_apply(Native *nt, Val *arg) {
    if (nt->mon && nt->marg == arg && (nt->mmv == metas_version || nt->mstable)) return nt->mres;
    int save = meta_blocked; meta_blocked = 0;
    Val *r = native_step(nt, arg);
    nt->marg = arg; nt->mres = r; nt->mmv = metas_version; nt->mon = 1; nt->mstable = !meta_blocked;
    meta_blocked |= save;
    return r;
}
static Val *native_step(Native *nt, Val *arg) {
    switch (nt->code) {
    case N_IH: return ih_apply(nt, arg);
    case N_CONST: return CAP(nt, 0);
    case N_LINE_DOM: { Val *pi = force(vapp(CAP(nt, 0), arg, 0)); if (pi->k != V_PI && pi->k != V_SIGMA) die("internal: domain of a non-function line"); return pi->dom; }
    case N_LINE_COD_V: {    /* λi. B_i (v i), cap: line, vfn */
        Val *pi = force(vapp(CAP(nt, 0), arg, 0)); if (pi->k != V_PI && pi->k != V_SIGMA) die("internal: codomain of a non-function line");
        return inst(&pi->clo, vapp(CAP(nt, 1), arg, 0));
    }
    case N_TRANSP_V: {      /* v i = transp (λj. A (i ∨ ~j)) (φ ∨ i) u1, cap: Aline, phi, u1 */
        Val *inner = vnative(N_LINE_IOR, 1, 0, 0, 2, CAP(nt, 0), arg);
        return vtransp(inner, ior(CAP(nt, 1), arg), CAP(nt, 2));
    }
    case N_LINE_IOR: {      /* i1==0: λj. line (j ∨ r); i1==1: λj. line (r ∨ ~j) */
        Val *r = CAP(nt, 1);
        return vapp(CAP(nt, 0), nt->i1 ? ior(r, ineg(arg)) : ior(arg, r), 0);
    }
    case N_LINE_IAND: return vapp(CAP(nt, 0), iand(CAP(nt, 1), arg), 0);   /* λj. line (i ∧ j) */
    case N_HCOMP_PI_SIDES: return vapp(force(vapp(CAP(nt, 0), arg, 0)), CAP(nt, 1), nt->i1);   /* λi. (u i) x */
    case N_PATH_HCOMP_SIDES: {   /* λi. [φ ↦ (u i) @ j, j ↦ y, ~j ↦ x], cap: u, phi, j, x, y */
        VBranch br[3];
        br[0].phi = CAP(nt, 1); br[0].v = vpapp(force(vapp(CAP(nt, 0), arg, 0)), CAP(nt, 2), CAP(nt, 3), CAP(nt, 4));
        br[1].phi = CAP(nt, 2); br[1].v = CAP(nt, 4);
        br[2].phi = ineg(CAP(nt, 2)); br[2].v = CAP(nt, 3);
        return vsys(br, 3);
    }
    case N_LINE_PATH_AT: {       /* λi. (line i).line @ j  (the type of paths at i, applied to j), cap: line, j */
        Val *pt = force(vapp(CAP(nt, 0), arg, 0)); if (pt->k != V_PATHP) die("internal: path line expected");
        return vapp(pt->a, CAP(nt, 1), 0);
    }
    case N_PATH_TRANSP_SIDES: {  /* λi. [φ ↦ p @ j, ~j ↦ x_i, j ↦ y_i], cap: line, phi, p, j */
        Val *pt = force(vapp(CAP(nt, 0), arg, 0)); if (pt->k != V_PATHP) die("internal: path line expected");
        Val *p0 = vapp(CAP(nt, 0), izero(), 0);
        VBranch br[3];
        br[0].phi = CAP(nt, 1); br[0].v = vpapp(CAP(nt, 2), CAP(nt, 3), p0->b, p0->c);
        br[1].phi = ineg(CAP(nt, 3)); br[1].v = pt->b;
        br[2].phi = CAP(nt, 3); br[2].v = pt->c;
        return vsys(br, 3);
    }
    case N_FWD_SIDES: {          /* λi. fwd line i (u i), mapped over the partial element */
        Val *ui = vapp(CAP(nt, 1), arg, 0);
        struct { Val *line, *i; } d = { CAP(nt, 0), arg };
        Val *(*fn)(Val *, void *) = NULL; (void)fn;
        if (ui->k != V_SYS) return vfwd(d.line, d.i, ui);
        VBranch *br = xalloc((ui->nbr + 1) * sizeof(VBranch));
        for (int k = 0; k < ui->nbr; k++) { br[k].phi = ui->br[k].phi; br[k].v = vfwd(d.line, d.i, ui->br[k].v); }
        return vsys(br, ui->nbr);
    }
    case N_FILL_SIDES: {         /* λj. [φ ↦ u (i∧j), ~i ↦ u0], cap: u, u0, i, phi */
        VBranch br[2];
        br[0].phi = CAP(nt, 3); br[0].v = vapp(CAP(nt, 0), iand(CAP(nt, 2), arg), 0);
        br[1].phi = ineg(CAP(nt, 2)); br[1].v = CAP(nt, 1);
        return vsys(br, 2);
    }
    case N_FILL: {               /* i1==1: hfill (cap: A, phi, u, u0); i1==0: fill (cap: line, phi, u, u0) */
        Val *sides = vnative(N_FILL_SIDES, 0, 0, 0, 4, CAP(nt, 2), CAP(nt, 3), arg, CAP(nt, 1));
        Val *phi2 = ior(CAP(nt, 1), ineg(arg));
        if (nt->i1) return vhcomp(CAP(nt, 0), phi2, sides, CAP(nt, 3));
        return vcomp(vnative(N_LINE_IAND, 0, 0, 0, 2, CAP(nt, 0), arg), phi2, sides, CAP(nt, 3));
    }
    case N_TFILL: return vtransp(vnative(N_LINE_IAND, 0, 0, 0, 2, CAP(nt, 0), arg), ior(CAP(nt, 1), ineg(arg)), CAP(nt, 2));
    case N_DATA_ARG_LINE: {      /* λi. A_j evaluated at (params of line i, fills k<j at i); cap: line, fill_0..fill_{j-1}; i1=con, i2=j */
        Val *Di = force(vapp(CAP(nt, 0), arg, 0)); if (Di->k != V_DATA) die("internal: data line expected");
        Con *C = con_at(nt->i1, Di->lvl); int np = datas[C->data].nparams;
        Env *e = NULL;
        for (int i = 0; i < np; i++) e = env_push(e, Di->args.a[i].v);
        for (int k = 0; k < nt->i2; k++) e = env_push(e, vapp(CAP(nt, 1 + k), arg, 0));
        return eval(e, C->args[nt->i2].ty);
    }
    case N_ELIM_MOTIVE_LINE: {   /* λk. P idx (fill k); cap: P, idx.., fill; i1 = #idx */
        Val *P = CAP(nt, 0);
        for (int j = 0; j < nt->i1; j++) P = vapp(P, CAP(nt, 1 + j), 1);
        return vapp(P, vapp(CAP(nt, 1 + nt->i1), arg, 0), 0);
    }
    case N_ELIM_SIDES: return vsys_map(vapp(CAP(nt, 1), arg, 0), apply_to, CAP(nt, 0));   /* λk. elim .. (u k) */
    case N_SUBST: return subst_val(CAP(nt, 0), nt->i1, arg->iv);                    /* λi. v[F := i] */
    case N_GLUE_T: {                                                                  /* λi. fst (Te_i), total on its face */
        Val *Te = vsys_at(subst_val(CAP(nt, 0), nt->i1, arg->iv), NULL);
        if (!Te) die("internal: Glue: the glued type is used outside its face");
        return vproj(Te, 1);
    }
    case N_UNGLUE_U0: return vunglue(subst_val(CAP(nt, 0), nt->i1, arg->iv), subst_val(CAP(nt, 1), nt->i1, arg->iv), subst_val(CAP(nt, 2), nt->i1, arg->iv), CAP(nt, 3));
    case N_GLUE_TR_SIDES: {
        TrSides d = { CAP(nt, 0), CAP(nt, 1), CAP(nt, 2), CAP(nt, 3), CAP(nt, 4), arg, nt->i1 };
        Val *phis[2] = { CAP(nt, 0), CAP(nt, 1) };
        return vsys_faces(2, phis, glue_tr_body, &d);
    }
    case N_GLUE_A1P_SIDES: {
        A1pData d = { CAP(nt, 0), CAP(nt, 1), CAP(nt, 2), CAP(nt, 3), CAP(nt, 4), CAP(nt, 5), arg };
        Val *phis[2] = { CAP(nt, 0), CAP(nt, 1) };
        return vsys_faces(2, phis, glue_a1p_body, &d);
    }
    case N_GLUE_HF: {
        HfData d = { CAP(nt, 0), CAP(nt, 1), CAP(nt, 2), CAP(nt, 3), arg };
        Val *phis[1] = { CAP(nt, 4) };
        return vsys_faces(1, phis, glue_hf_body, &d);
    }
    case N_GLUE_HC_SIDES: {
        HcData d = { CAP(nt, 0), CAP(nt, 1), CAP(nt, 2), CAP(nt, 3), CAP(nt, 4), CAP(nt, 5), arg };
        Val *phis[2] = { CAP(nt, 3), CAP(nt, 1) };
        return vsys_faces(2, phis, glue_hc_body, &d);
    }
    case N_GCOMP_SIDES: {
        Caps c = { 5, { CAP(nt, 0), CAP(nt, 1), CAP(nt, 2), CAP(nt, 3), arg } };
        Val *phis[2] = { CAP(nt, 1), ineg(CAP(nt, 1)) };
        return vsys_faces(2, phis, gcomp_body, &c);
    }
    case N_HITTR_SIDES: {        /* λj. [ psi_k -> squeeze of the boundary at stage ~j, phi -> u0 ]; cap: line, phi, u0, fills..; i1 = con */
        int np = datas[cons[nt->i1].data].nparams;
        Val *line = CAP(nt, 0), *phi = CAP(nt, 1), *u0 = CAP(nt, 2);
        Val *stage = ineg(arg);
        Val *Dst = vapp(line, stage, 0);   /* the type at the stage: its parameters */
        Con *C = con_at(nt->i1, Dst->lvl);
        Env *env = NULL;
        for (int i = 0; i < np; i++) env = env_push(env, Dst->args.a[i].v);
        for (int j = 0; j < C->nargs; j++) env = env_push(env, vapp(CAP(nt, 3 + j), stage, 0));
        for (int q = 0; q < C->nint; q++) env = env_push(env, u0->args.a[np + C->nargs + q].v);
        Val *bsys = eval(env, C->boundary);
        Native *sq = xalloc(sizeof *sq); sq->code = 0;
        vl_push(&sq->cap, vnative(N_LINE_IOR, 0, 0, 0, 2, line, stage), 0); vl_push(&sq->cap, ior(stage, phi), 0);
        Val *sqz = vsys_map(bsys, transp_branch, sq);
        VBranch br[2]; int n = 0;
        if (sqz->k == V_SYS) { VBranch *b2 = xalloc((sqz->nbr + 2) * sizeof(VBranch)); memcpy(b2, sqz->br, sqz->nbr * sizeof(VBranch)); n = sqz->nbr; b2[n].phi = phi; b2[n].v = u0; return vsys(b2, n + 1); }
        br[n].phi = ione(); br[n].v = sqz; n++;
        br[n].phi = phi; br[n].v = u0; n++;
        return vsys(br, n);
    }
    case N_ELIM_PATH_IH: {       /* λk. elim base.. idx.. (p @ k); cap: base (np+1+ncons values), idx.., p, x, y; i1 = data */
        int nb = nt->cap.n - 3;
        VList a2 = {0}; for (int i = 0; i < nb; i++) vl_push(&a2, CAP(nt, i), nt->cap.a[i].irr);
        vl_push(&a2, vpapp(CAP(nt, nb), arg, CAP(nt, nb + 1), CAP(nt, nb + 2)), 0);
        return elim_apply_list(nt->i1, &a2);
    }
    case N_TRANSP_MAP: return vsys_map(vapp(CAP(nt, 2), arg, 0), transp_branch, nt);   /* λi. transp line phi (u i) over the partial element; cap: line, phi, u */
    case N_SYS_PROJ: {           /* λi. proj_k (u i) over the partial element; cap: u; i1 = k */
        Val *ui = force(vapp(CAP(nt, 0), arg, 0));
        int k = nt->i1;
        return vsys_map(ui, proj_arg, &k);
    }
    }
    die("internal: unknown native closure %d", nt->code);
    return NULL;
}

/* all branches of the partial element u (at a fresh i) are constructor c? */
static int sides_all_con(Val *u, int con) {
    u = force(u);   /* a rigid definition application unfolds to the partial element */
    Val *ui = vapp(u, fresh_ivar(), 0);
    if (ui->k == V_NUM) ui = num_view(ui);
    if (ui->k == V_SYS) {
        for (int i = 0; i < ui->nbr; i++) { Val *w = ui->br[i].v; if (w->k == V_NUM) w = num_view(w); if (w->k != V_CON || w->n != con) return 0; }
        return 1;
    }
    return ui->k == V_CON && ui->n == con;
}

/* the lazily transported / composed irrelevant component of a pair (M16a); the argument is unused */
static Val *transp_snd_thunk(void *data, Val *unused) {
    (void)unused; Caps *cp = data; Val *line = cp->v[0], *phi = cp->v[1], *u0 = cp->v[2], *aline = cp->v[3];
    Val *fst = vproj(u0, 1);
    return vtransp(vnative(N_LINE_COD_V, 0, 0, 0, 2, line, vtfill(aline, phi, fst)), phi, vproj(u0, 2));
}
static Val *hcomp_snd_thunk(void *data, Val *unused) {
    (void)unused; Caps *cp = data; Val *A = cp->v[0], *phi = cp->v[1], *u = cp->v[2], *u0 = cp->v[3], *ufst = cp->v[4];
    Val *fst = vproj(u0, 1);
    Val *usnd = vnative(N_SYS_PROJ, -2, 0, 0, 1, u);
    Val *fill = vnative(N_FILL, 1, 0, 0, 4, A->dom, phi, ufst, fst);
    return vcomp(vnative(N_LINE_COD_V, 0, 0, 0, 2, vnative(N_CONST, 0, 0, 0, 1, A), fill), phi, usnd, vproj(u0, 2));
}
Val *vtransp(Val *line, Val *phi, Val *u0) {
    if (iv_is_one(phi->iv)) return u0;
    u0 = force(u0);
    Val *fi = fresh_ivar();
    Val *Ai = force(vapp(line, fi, 0));
    if (Ai->k == V_NEU && Ai->h == H_META) die("transport along a type that is not known yet (an implicit argument still to be inferred); write it, f {e} ..");
    switch (Ai->k) {
    case V_U: return u0;
    case V_PI: {
        if (Ai->isi) {   /* (i : I) -> B i x : no transport of the argument */
            Val *(*fn)(void *, Val *) = NULL; (void)fn;
            /* λu1. transp (λi. B_i u1) φ (f u1) */
            struct Lam2 { Val *line, *phi, *f; }; (void)sizeof(struct Lam2);
        }
        /* λu1. transp (λi. B_i (v i)) φ (f (v i0)) with v i = transp (λj. A (i ∨ ~j)) (φ ∨ i) u1  (v i = u1 for an interval domain) */
        Val *res = mkval(V_LAM); res->name = "x";
        Native *nt = xalloc(sizeof *nt); nt->code = N_CONST; /* placeholder, replaced below */
        (void)nt;
        /* build as a native closure of code N_TRANSP_PI: implemented inline via a small trampoline */
        Caps *tp = xalloc(sizeof *tp); tp->n = 3; tp->v[0] = line; tp->v[1] = phi; tp->v[2] = u0; tp->v[3] = Ai->isi ? vi(iv_one()) : vi(iv_zero());
        extern Val *transp_pi_apply(void *, Val *);
        res->clo.fn = transp_pi_apply; res->clo.data = tp;
        return res;
    }
    case V_PATHP: {
        /* λj. comp (λi. A_i @ j) (φ ∨ j ∨ ~j) [φ ↦ p @ j, ~j ↦ x_i, j ↦ y_i] (p @ j) */
        Caps *tp = xalloc(sizeof *tp); tp->n = 3; tp->v[0] = line; tp->v[1] = phi; tp->v[2] = u0;
        extern Val *transp_path_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "j"; res->isi = 1; res->clo.fn = transp_path_apply; res->clo.data = tp;
        return res;
    }
    case V_GLUE: return transp_glue(line, phi, u0, Ai, fi);
    case V_SIGMA: {
        /* (transp A φ (fst p), transp (λi. B_i (fill i)) φ (snd p)) with fill the transport filler of the first component */
        Val *aline = vnative(N_LINE_DOM, 0, 0, 0, 1, line);
        Val *fst = vproj(u0, 1);
        Val *res = mkval(V_PAIR); res->irr = u0->irr; res->n = u0->n;
        res->a = vtransp(aline, phi, fst);
        if (u0->irr) {   /* lazily: the proof is transported only if it is ever projected */
            Caps *cp = xalloc(sizeof *cp); cp->n = 4; cp->v[0] = line; cp->v[1] = phi; cp->v[2] = u0; cp->v[3] = aline;
            res->b = NULL; res->clo.fn = transp_snd_thunk; res->clo.data = cp;
        } else res->b = vtransp(vnative(N_LINE_COD_V, 0, 0, 0, 2, line, vtfill(aline, phi, fst)), phi, vproj(u0, 2));
        return res;
    }
    case V_DATA: {
        Data *D = data_at(Ai->n, Ai->lvl);
        if (D->nparams + D->nidx == 0) return u0;
        if (D->hit && u0->k == V_NEU && u0->h == H_HCOMP && u0->a->k == V_DATA) {   /* transp of a formal composition: the composition of the transports */
            Val *D1 = vapp(line, ione(), 0);
            return vhcomp(D1, u0->b, vnative(N_TRANSP_MAP, 0, 0, 0, 3, line, phi, u0->c), vtransp(line, phi, u0->dom));
        }
        if (u0->k != V_CON) return neu_transp(line, phi, u0);
        Con *C = con_at(u0->n, u0->lvl);
        int np = D->nparams;
        /* transport each argument along its own line, with fillers for the earlier ones */
        Val **fills = xalloc((C->nargs + 1) * sizeof(Val *));
        Val *res = mkval(V_CON); res->n = u0->n; res->lvl = u0->lvl;
        Val *D1 = vapp(line, ione(), 0);
        for (int i = 0; i < np; i++) vl_push(&res->args, D1->args.a[i].v, 1);
        for (int j = 0; j < C->nargs; j++) {
            Native *nt = xalloc(sizeof *nt); nt->code = N_DATA_ARG_LINE; nt->i1 = u0->n; nt->i2 = j;
            vl_push(&nt->cap, line, 0); for (int k = 0; k < j; k++) vl_push(&nt->cap, fills[k], 0);
            Val *aline = mkval(V_LAM); aline->clo.fn = nfn; aline->clo.data = nt; aline->isi = 1; aline->name = "i";
            Val *aj = u0->args.a[np + j].v;
            vl_push(&res->args, vtransp(aline, phi, aj), C->args[j].irr);
            fills[j] = vtfill(aline, phi, aj);
        }
        if (C->nint > 0) {   /* a path constructor keeps its interval arguments (CHM 3.3: merid (transp a) r) */
            Val *r = mkval(V_CON); r->n = res->n; r->lvl = res->lvl;
            for (int i = 0; i < res->args.n; i++) vl_push_arg(&r->args, res->args.a[i]);
            for (int q = 0; q < C->nint; q++) vl_push(&r->args, u0->args.a[np + C->nargs + q].v, 0);
            res = r;
            if (C->bparams) {
                /* the boundary mentions the parameters (CHM 3.3.5, pushouts): the naive result's boundary b(p1, a', r) is not the
                   transported boundary; correct it with a composition whose sides squeeze the boundary at every stage:
                     hcomp^j (D p1) [ psi_k -> transp (i. D (p (i \/ ~j))) (~j \/ phi) (b_k (p (~j), fill_a (~j), r)),  phi -> c a r ] (c a' r) */
                Native *nt = xalloc(sizeof *nt); nt->code = N_HITTR_SIDES; nt->i1 = u0->n;
                vl_push(&nt->cap, line, 0); vl_push(&nt->cap, phi, 0); vl_push(&nt->cap, u0, 0);
                for (int j = 0; j < C->nargs; j++) vl_push(&nt->cap, fills[j], 0);
                Val *sides = mkval(V_LAM); sides->clo.fn = nfn; sides->clo.data = nt; sides->isi = 1; sides->name = "j";
                Env *env = NULL; for (int i = 0; i < u0->args.n; i++) env = env_push(env, u0->args.a[i].v);
                Val *bsys = eval(env, C->boundary);
                IVal psi = iv_zero();
                if (bsys->k == V_SYS) { for (int i = 0; i < bsys->nbr; i++) psi = iv_or(psi, bsys->br[i].phi->iv); } else psi = iv_one();
                if (D->nidx > 0) {   /* the composition lives at the line's index, which the transported constructor must reach */
                    Env *e2 = NULL; for (int i = 0; i < res->args.n; i++) e2 = env_push(e2, res->args.a[i].v);
                    for (int j = 0; j < D->nidx; j++)
                        if (!conv(fresh_level, eval(e2, C->ridx[j]), D1->args.a[np + j].v)) return neu_transp(line, phi, u0);
                }
                return vhcomp(D1, vi(iv_or(psi, phi->iv)), sides, res);
            }
        }
        if (D->nidx > 0) {   /* the transported constructor's indices must agree with the line's */
            Env *e = NULL; for (int i = 0; i < res->args.n; i++) e = env_push(e, res->args.a[i].v);
            for (int j = 0; j < D->nidx; j++)
                if (!conv(fresh_level, eval(e, C->ridx[j]), D1->args.a[np + j].v)) return neu_transp(line, phi, u0);
        }
        return res;
    }
    default: return neu_transp(line, phi, u0);
    }
}
Val *transp_pi_apply(void *data, Val *u1) {
    Caps *tp = data; Val *line = tp->v[0], *phi = tp->v[1], *f = tp->v[2]; int isi = iv_is_one(tp->v[3]->iv);
    Val *v;
    if (isi) v = vnative(N_CONST, 0, 0, 0, 1, u1);
    else v = vnative(N_TRANSP_V, 0, 0, 0, 3, vnative(N_LINE_DOM, 0, 0, 0, 1, line), phi, u1);
    Val *bline = vnative(N_LINE_COD_V, 0, 0, 0, 2, line, v);
    return vtransp(bline, phi, vapp(f, vapp(v, izero(), 0), 0));
}
Val *transp_path_apply(void *data, Val *j) {
    Caps *tp = data; Val *line = tp->v[0], *phi = tp->v[1], *p = tp->v[2];
    Val *p0 = vapp(line, izero(), 0);
    Val *aline = vnative(N_LINE_PATH_AT, 0, 0, 0, 2, line, j);
    Val *sides = vnative(N_PATH_TRANSP_SIDES, 0, 0, 0, 4, line, phi, p, j);
    return vcomp(aline, ior(phi, ior(j, ineg(j))), sides, vpapp(p, j, p0->b, p0->c));
}

Val *vhcomp(Val *A, Val *phi, Val *u, Val *u0) {
    if (iv_is_one(phi->iv)) { Val *t = vsys_at(force(vapp(u, ione(), 0)), NULL); if (!t) die("internal: total system without a total branch"); return t; }
    A = force(A); u0 = force(u0);
    if (A->k == V_NEU && A->h == H_META) die("hcomp at a type that is not known yet (an implicit argument still to be inferred); write it, f {e} ..");
    switch (A->k) {
    case V_PI: {
        Caps *hp = xalloc(sizeof *hp); hp->n = 4; hp->v[0] = A; hp->v[1] = phi; hp->v[2] = u; hp->v[3] = u0;
        extern Val *hcomp_pi_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "x"; res->isi = A->isi; res->clo.fn = hcomp_pi_apply; res->clo.data = hp;
        return res;
    }
    case V_PATHP: {
        Caps *hp = xalloc(sizeof *hp); hp->n = 4; hp->v[0] = A; hp->v[1] = phi; hp->v[2] = u; hp->v[3] = u0;
        extern Val *hcomp_path_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "j"; res->isi = 1; res->clo.fn = hcomp_path_apply; res->clo.data = hp;
        return res;
    }
    case V_SIGMA: {
        /* (hcomp A φ (fst u) (fst u0), comp (λi. B (hfill A φ (fst u) (fst u0) i)) φ (snd u) (snd u0)) */
        Val *ufst = vnative(N_SYS_PROJ, -1, 0, 0, 1, u);
        Val *fst = vproj(u0, 1);
        Val *res = mkval(V_PAIR); res->irr = u0->irr; res->n = u0->n;
        res->a = vhcomp(A->dom, phi, ufst, fst);
        if (u0->irr) {
            Caps *cp = xalloc(sizeof *cp); cp->n = 5; cp->v[0] = A; cp->v[1] = phi; cp->v[2] = u; cp->v[3] = u0; cp->v[4] = ufst;
            res->b = NULL; res->clo.fn = hcomp_snd_thunk; res->clo.data = cp;
        } else {
            Val *usnd = vnative(N_SYS_PROJ, -2, 0, 0, 1, u);
            Val *fill = vnative(N_FILL, 1, 0, 0, 4, A->dom, phi, ufst, fst);
            res->b = vcomp(vnative(N_LINE_COD_V, 0, 0, 0, 2, vnative(N_CONST, 0, 0, 0, 1, A), fill), phi, usnd, vproj(u0, 2));
        }
        return res;
    }
    case V_GLUE: return hcomp_glue(A, phi, u, u0);
    case V_U: {   /* hcomp in the universe is the Glue type of the lid, glued along transport back down the sides (CCHM 6) */
        Caps c = { 0, { u } }; c.l = A->lvl;
        Val *Te = vsys_faces(1, &phi, hcompU_body, &c);
        Val *g = vglue(u0, phi, Te); if (g->k == V_GLUE) g->lvl = A->lvl;
        return g;
    }
    case V_DATA: {
        Data *D = data_at(A->n, A->lvl);
        if (D->nidx > 0 || D->hit) return neu_hcomp(A, phi, u, u0);
        if (u0->k == V_NUM) u0 = num_view(u0);
        if (u0->k != V_CON || !sides_all_con(u, u0->n)) return neu_hcomp(A, phi, u, u0);
        Con *C = con_at(u0->n, u0->lvl); int np = D->nparams;
        Val *res = mkval(V_CON); res->n = u0->n; res->lvl = u0->lvl;
        for (int i = 0; i < np; i++) vl_push(&res->args, A->args.a[i].v, 1);
        Val **fills = xalloc((C->nargs + 1) * sizeof(Val *));
        Val *cline = vnative(N_CONST, 0, 0, 0, 1, A);
        for (int j = 0; j < C->nargs; j++) {
            Native *nt = xalloc(sizeof *nt); nt->code = N_DATA_ARG_LINE; nt->i1 = u0->n; nt->i2 = j;
            vl_push(&nt->cap, cline, 0); for (int k = 0; k < j; k++) vl_push(&nt->cap, fills[k], 0);
            Val *aline = mkval(V_LAM); aline->clo.fn = nfn; aline->clo.data = nt; aline->isi = 1; aline->name = "i";
            Val *sides = vnative(N_SYS_PROJ, np + j, 0, 0, 1, u);
            Val *aj = u0->args.a[np + j].v;
            vl_push(&res->args, vcomp(aline, phi, sides, aj), C->args[j].irr);
            fills[j] = vfill(aline, phi, sides, aj);
        }
        return res;
    }
    default: return neu_hcomp(A, phi, u, u0);
    }
}
Val *hcomp_pi_apply(void *data, Val *x) {
    Caps *hp = data; Val *A = hp->v[0], *phi = hp->v[1], *u = hp->v[2], *u0 = hp->v[3];
    Val *B = inst(&A->clo, x);
    return vhcomp(B, phi, vnative(N_HCOMP_PI_SIDES, A->irr, 0, 0, 2, u, x), vapp(u0, x, A->irr));
}
Val *hcomp_path_apply(void *data, Val *j) {
    Caps *hp = data; Val *A = hp->v[0], *phi = hp->v[1], *u = hp->v[2], *u0 = hp->v[3];
    Val *Aj = vapp(A->a, j, 0);
    Val *sides = vnative(N_PATH_HCOMP_SIDES, 0, 0, 0, 5, u, phi, j, A->b, A->c);
    return vhcomp(Aj, ior(phi, ior(j, ineg(j))), sides, vpapp(u0, j, A->b, A->c));
}


/* ---- Glue types (CCHM section 6; the Kan operations follow Agda's Glue.hs) ---- */
static Val *builtin_at(const char *name, LVal L) {
    for (int i = ndefs - 1; i >= 0; i--) if (!strcmp(defs[i].name, name)) return def_at(i, L);
    die("internal: the prelude definition %s is needed", name);
    return NULL;
}
Val *vglue(Val *A, Val *phi, Val *Te) {
    if (iv_is_one(phi->iv)) { Val *t = vsys_at(Te, NULL); if (t) return vproj(t, 1); }
    Val *v = mkval(V_GLUE); v->a = A; v->b = phi; v->c = Te; return v;
}
Val *vglueel(Val *ts, Val *a, Val *G) {
    if (G->k != V_GLUE) { Val *t = vsys_at(ts, NULL); if (!t) die("internal: glue on a total face without a total element"); return t; }
    Val *v = mkval(V_GLUEEL); v->a = ts; v->b = a; v->c = G; return v;
}
static Val *equiv_fun(Val *Te_total) { return vproj(vproj(Te_total, 2), 1); }
Val *vunglue(Val *A, Val *phi, Val *Te, Val *b) {
    if (iv_is_one(phi->iv)) { Val *t = vsys_at(Te, NULL); if (t) return vapp(equiv_fun(t), b, 0); }
    b = force(b);   /* through a rigid definition application, as vhcomp forces its type and base: unglue (g i1) with g i1 := glue [] a is a (M20 F4 found it stuck) */
    if (b->k == V_GLUEEL) return b->b;
    if (b->k == V_SYS) {
        VBranch *br = xalloc((b->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < b->nbr; i++) { br[i].phi = b->br[i].phi; br[i].v = vunglue(A, phi, Te, b->br[i].v); }
        return vsys(br, b->nbr);
    }
    Val *v = mkval(V_NEU); v->h = H_UNGLUE; v->a = A; v->b = phi; v->c = Te; v->dom = b; return v;
}
/* a system whose k-th part lives on the faces of phis[k]; each branch is computed under the restriction to its face,
   so that partial data (a Glue type's T and e) is total where the branch is used */
static Val *vsys_faces(int nb, Val **phis, SysBody body, void *data) {
    int cap = 4, n = 0; VBranch *br = xalloc(cap * sizeof(VBranch));
    for (int k = 0; k < nb; k++) {
        Face *fs; int nf = iv_faces(phis[k]->iv, &fs);
        for (int i = 0; i < nf; i++) {
            if (n == cap) { cap *= 2; VBranch *b2 = xalloc(cap * sizeof(VBranch)); memcpy(b2, br, n * sizeof(VBranch)); br = b2; }
            br[n].phi = vi(face_iv(&fs[i])); br[n].v = body(k, &fs[i], data); n++;
        }
    }
    return vsys(br, n);
}
#define R(x) restrict_val((x), f)
static Val *at(Val *v, int F, Val *i) { return subst_val(v, F, i->iv); }

/* gcomp: composition whose base is also propagated on ~phi, so that no empty systems arise (Agda's mkGComp) */
static Val *gcomp_body(int k, const Face *f, void *data) {
    Caps *c = data; Val *line = R(c->v[0]), *u = R(c->v[2]), *u0 = R(c->v[3]), *i = R(c->v[4]);
    return k == 0 ? vfwd(line, i, vapp(u, i, 0)) : vfwd(line, izero(), u0);
}
static Val *vgcomp(Val *line, Val *phi, Val *u, Val *u0) {
    return vhcomp(vapp(line, ione(), 0), ior(phi, ineg(phi)), vnative(N_GCOMP_SIDES, 0, 0, 0, 4, line, phi, u, u0), vfwd(line, izero(), u0));
}

/* transp (λi. Glue A_i φ_i Te_i) ψ u0, with the components given at the fresh interval variable F */
static Val *glue_tr_body(int k, const Face *f, void *data) {
    TrSides *d = data; Val *i = R(d->i);
    if (k == 0) return vapp(R(d->ungl), i, 0);
    Val *Te_i = vsys_at(at(R(d->Teg), d->F, i), NULL);
    if (!Te_i) die("internal: Glue transport: the glued type is not total on its face");
    return vapp(equiv_fun(Te_i), vapp(R(d->tf), i, 0), 0);
}
typedef struct { Val *u0, *tf, *a1; } PeData;
static Val *pe_body(int k, const Face *f, void *data) {
    PeData *d = data; Val *p = mkval(V_PAIR);
    p->a = k == 0 ? R(d->u0) : vapp(R(d->tf), ione(), 0);
    Val *c = vnative(N_CONST, 0, 0, 0, 1, R(d->a1)); p->b = c;
    return p;
}
typedef struct { Val *Te1, *A1, *a1, *psi, *forall, *u0, *tf; LVal lvl; } FibData;
static Val *glue_fiber_body(int k, const Face *f, void *data) {
    FibData *d = data; (void)k;
    Val *Te = vsys_at(R(d->Te1), NULL);
    if (!Te) die("internal: Glue transport: the glued type is not total at i1 on its face");
    Val *T1 = vproj(Te, 1), *w = vproj(Te, 2), *A1 = R(d->A1), *a1 = R(d->a1);
    Val *psi = R(d->psi), *forall = R(d->forall);
    PeData pd = { R(d->u0), R(d->tf), a1 };
    Val *phis[2] = { psi, forall };
    Val *pe = vsys_faces(2, phis, pe_body, &pd);
    Val *ep = builtin_at("equivProof", d->lvl);
    Val *fib = vapp(vapp(vapp(vapp(vapp(vapp(ep, T1, 0), A1, 0), w, 0), a1, 0), ior(psi, forall), 0), pe, 0);
    if (fib->k == V_INS) return fib->a;
    Val *fiberT = vapp(vapp(vapp(vapp(builtin_at("fiber", d->lvl), T1, 0), A1, 0), vproj(w, 1), 0), a1, 0);
    return vouts(fiberT, ior(psi, forall), pe, fib);
}
static Val *glue_a1p_body(int k, const Face *f, void *data) {
    A1pData *d = data;
    if (k == 1) return R(d->a1);
    Val *alpha = vsys_at(R(d->alphas), NULL), *t1 = vsys_at(R(d->ts), NULL), *Te = vsys_at(R(d->Te1), NULL);
    if (!alpha || !t1 || !Te) die("internal: Glue transport: partial fibre not total on its face");
    Val *x = vapp(equiv_fun(Te), t1, 0);
    return vpapp(alpha, ineg(R(d->j)), x, R(d->a1));
}
static Val *proj1(Val *v, void *d) { (void)d; return vproj(v, 1); }
static Val *proj2(Val *v, void *d) { (void)d; return vproj(v, 2); }
static Val *transp_glue(Val *line, Val *psi, Val *u0, Val *Ag, Val *fiv) {
    (void)line;
    int F = fiv->iv.c[0].l[0].var;
    Val *Ab = Ag->a, *phig = Ag->b, *Teg = Ag->c;
    Val *forall = vi(iv_forall(phig->iv, F));
    Val *lineA = vnative(N_SUBST, F, 0, 0, 1, Ab);
    Val *lineT = vnative(N_GLUE_T, F, 0, 0, 1, Teg);
    Val *ungl = vnative(N_UNGLUE_U0, F, 0, 0, 4, Ab, phig, Teg, u0);
    Val *tf = vtfill(lineT, psi, u0);
    Val *sides = vnative(N_GLUE_TR_SIDES, F, 0, 0, 5, psi, forall, ungl, Teg, tf);
    Val *a1 = vgcomp(lineA, ior(psi, forall), sides, vapp(ungl, izero(), 0));
    Val *phi1 = vi(iv_subst(phig->iv, F, iv_one()));
    Val *Te1 = subst_val(Teg, F, iv_one()), *A1 = subst_val(Ab, F, iv_one());
        FibData fd = { Te1, A1, a1, psi, forall, u0, tf, Ag->lvl };
    Val *fibsys = vsys_faces(1, &phi1, glue_fiber_body, &fd);
    Val *ts = vsys_map(fibsys, proj1, NULL), *alphas = vsys_map(fibsys, proj2, NULL);
    Val *a1p = vhcomp(A1, ior(phi1, psi), vnative(N_GLUE_A1P_SIDES, 0, 0, 0, 6, phi1, psi, alphas, ts, Te1, a1), a1);
    Val *G1 = subst_val(Ag, F, iv_one()); if (G1->k == V_GLUE) G1->lvl = Ag->lvl;
    return vglueel(ts, a1p, G1);
}
/* hcomp ψ u u0 at Glue A φ Te */
static Val *glue_hf_body(int k, const Face *f, void *data) {
    HfData *d = data; (void)k;
    Val *Te = vsys_at(R(d->Te), NULL); if (!Te) die("internal: Glue hcomp: the glued type is not total on its face");
    Val *fill = vnative(N_FILL, 1, 0, 0, 4, vproj(Te, 1), R(d->psi), R(d->u), R(d->u0));
    return vapp(fill, R(d->i), 0);
}
static Val *glue_hc_body(int k, const Face *f, void *data) {
    HcData *d = data; Val *i = R(d->i);
    if (k == 0) return vunglue(R(d->Ab), R(d->phi), R(d->Te), vapp(R(d->u), i, 0));
    Val *Te = vsys_at(R(d->Te), NULL); if (!Te) die("internal: Glue hcomp: the glued type is not total on its face");
    Val *t = vsys_at(vapp(R(d->tfs), i, 0), NULL); if (!t) die("internal: Glue hcomp: filler not total on its face");
    return vapp(equiv_fun(Te), t, 0);
}
static Val *hcompU_body(int k, const Face *f, void *data) {
    Caps *c = data; Val *u = restrict_val(c->v[0], f);
    (void)k;
    Val *p = mkval(V_PAIR);
    p->a = vapp(u, ione(), 0);                                        /* the type at the lid */
    p->b = vapp(builtin_at("transpEquiv", c->l), vnative(N_LINE_IOR, 1, 0, 0, 2, u, izero()), 0);   /* λi. u (i0 ∨ ~i) = u (~i): from the lid back to the base */
    return p;
}
static Val *hcomp_glue(Val *A, Val *psi, Val *u, Val *u0) {
    Val *Ab = A->a, *phi = A->b, *Te = A->c;
    Val *tfs = vnative(N_GLUE_HF, 0, 0, 0, 5, Te, psi, u, u0, phi);   /* the filler lives on phi, the Glue's face (M20: the face was read past the captures, a NULL) */
    Val *sides = vnative(N_GLUE_HC_SIDES, 0, 0, 0, 6, Ab, phi, Te, psi, u, tfs);
    Val *a1 = vhcomp(Ab, ior(psi, phi), sides, vunglue(Ab, phi, Te, u0));
    return vglueel(vapp(tfs, ione(), 0), a1, A);
}
#undef R

/* ---- quoting ---- */
static Term *quote_iv(int depth, IVal a) {
    if (a.n == 0) return mk(T_I0);
    Term *r = NULL;
    for (int i = 0; i < a.n; i++) {
        Term *c = NULL;
        for (int j = 0; j < a.c[i].n; j++) {
            int lvl = a.c[i].l[j].var;
            Term *l = lvl >= (1 << 20) ? mk_var(-1 - (lvl - (1 << 20))) : mk_var(depth - 1 - lvl);
            if (a.c[i].l[j].neg) l = mk_term(T_INEG, l, NULL, NULL, NULL);
            c = c ? mk_term(T_IAND, c, l, NULL, NULL) : l;
        }
        if (!c) c = mk(T_I1);
        r = r ? mk_term(T_IOR, r, c, NULL, NULL) : c;
    }
    return r;
}
/* The value a print-out should show. A pair's first component is a word over the naturals and may still be an
   unforced application - a value is canonical enough for conversion long before it is a printed normal form - so
   force it through. An irrelevant second component is a proof that prints as '.', and forcing it would mean walking
   a proof nobody reads. An explicit machine (frames on a heap stack, the child's result handed back in a register),
   not C recursion. */
typedef struct { Val *v, *w; int i; } NFrame;
static Stack nfst = { NULL, 0, 0, sizeof(NFrame) };   /* a Stack of the memory layer */
#define nfs ((NFrame *)nfst.p)
#define nnfs (nfst.n)
/* force v; a constructor with arguments or a pair opens a frame (1), anything else is the result (0) */
static int nf_open(Val *v, Val **ret) {
    v = force(v);
    Val *w;
    if (v->k == V_CON && v->args.n > 0) { w = mkval(V_CON); w->n = v->n; w->lvl = v->lvl; }
    else if (v->k == V_PAIR) { w = mkval(V_PAIR); w->irr = v->irr; w->n = v->n; }
    else { *ret = v; return 0; }
    NFrame fr = { v, w, 0 }; STACK_PUSH(&nfst, NFrame, fr);
    return 1;
}
Val *nf_force(Val *v0) {
    size_t base = nnfs; Val *ret = NULL; int have = 0;
    if (!nf_open(v0, &ret)) return ret;
    while (nnfs > base) {
        NFrame *fr = &nfs[nnfs - 1];
        if (fr->v->k == V_CON) {   /* a constructor's arguments, so a deferred elimination under suc prints as the number */
            if (fr->i < fr->v->args.n) {
                Arg a = fr->v->args.a[fr->i];
                if (!a.irr) {
                    if (!have) { if (nf_open(a.v, &ret)) continue; }
                    a.v = ret; have = 0;
                }
                fr = &nfs[nnfs - 1]; fr->w = vapply_arg(fr->w, &a); fr->i++;
                continue;
            }
        } else {   /* a pair: its first component, then (relevant) its second */
            if (fr->i == 0) {
                if (!have) { if (nf_open(fr->v->a, &ret)) continue; }
                fr = &nfs[nnfs - 1]; fr->w->a = ret; have = 0; fr->i = 1;
                continue;
            }
            if (fr->i == 1 && !fr->v->irr) {
                if (!have) { if (nf_open(pair_snd(fr->v), &ret)) continue; }
                fr = &nfs[nnfs - 1]; fr->w->b = ret; have = 0; fr->i = 2;
                continue;
            }
        }
        ret = fr->w; have = 1; nnfs--;   /* this frame is done: its value goes to the parent */
    }
    return ret;
}
/* Quoting: an explicit machine like conversion. Each node is made with its children's slots empty, and a task per
   slot fills it, in the order the recursion visited them (left to right, depth first). */
typedef struct { int depth; Val *v; Term **dst; } QTask;
static Stack qst = { NULL, 0, 0, sizeof(QTask) };   /* a Stack of the memory layer */
#define qs ((QTask *)qst.p)
#define nqs (qst.n)
static void qpush(int depth, Val *v, Term **dst) { QTask q = { depth, v, dst }; STACK_PUSH(&qst, QTask, q); }
static Term *quote_node(int depth, Val *v) {
    size_t from = nqs;
    Term *t = NULL;
    v = fmeta(v);   /* metas only: a rigid definition application quotes as the application (printing forces first) */
    switch (v->k) {
    case V_U: { int n; if (lv_is_const(v->lvl, &n)) return v->pre ? mk_upre(n) : mk_u(n); t = mk_u(0); t->pre = v->pre; t->a = quote_level(depth, v->lvl); return t; }
    case V_L: return quote_level(depth, v->lvl);
    case V_LEVEL: return mk_term(T_LEVEL, NULL, NULL, NULL, NULL);
    case V_INTERVAL: return mk(T_INTERVAL);
    case V_I: return quote_iv(depth, v->iv);
    case V_LAM: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        t = mk(T_LAM); t->name = v->name ? v->name : "x"; t->irr = v->irr; t->isi = v->isi; t->imp = v->imp;
        qpush(depth + 1, inst(&v->clo, x), &t->a);
        break;
    }
    case V_PI: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        t = mk(T_PI); t->name = v->name ? v->name : "_"; t->irr = v->irr; t->isi = v->isi; t->imp = v->imp;
        qpush(depth, v->dom, &t->a); qpush(depth + 1, inst(&v->clo, x), &t->b);
        break;
    }
    case V_PATHP: t = mk_term(T_PATHP, NULL, NULL, NULL, NULL); qpush(depth, v->a, &t->a); qpush(depth, v->b, &t->b); qpush(depth, v->c, &t->c); break;
    case V_PARTIAL: t = mk_term(T_PARTIAL, NULL, NULL, NULL, NULL); qpush(depth, v->a, &t->a); qpush(depth, v->b, &t->b); break;
    case V_SUB: t = mk_term(T_SUB, NULL, NULL, NULL, NULL); qpush(depth, v->a, &t->a); qpush(depth, v->b, &t->b); qpush(depth, v->c, &t->c); break;
    case V_INS: t = mk_term(T_INS, NULL, NULL, NULL, NULL); qpush(depth, v->a, &t->a); break;
    case V_SIGMA:
        t = mk_term(T_SIGMA, NULL, NULL, NULL, NULL); t->name = v->name ? v->name : "_"; t->irr = v->irr;
        qpush(depth, v->dom, &t->a); qpush(depth + 1, inst(&v->clo, vvar(depth)), &t->b);
        break;
    case V_PAIR:   /* an irrelevant component is elided from the normal form */
        t = mk_term(T_PAIR, NULL, v->irr ? mk_term(T_IRR, NULL, NULL, NULL, NULL) : NULL, NULL, NULL); t->irr = v->irr; t->n = v->n;
        qpush(depth, v->a, &t->a); if (!v->irr) qpush(depth, v->b, &t->b);
        break;
    case V_IRR: return mk_term(T_IRR, NULL, NULL, NULL, NULL);
    case V_GLUE:
        t = mk_term(T_GLUE, NULL, NULL, NULL, NULL); if (!lv_is_const(v->lvl, &t->n)) t->d = quote_level(depth, v->lvl);
        qpush(depth, v->a, &t->a); qpush(depth, v->b, &t->b); qpush(depth, v->c, &t->c);
        break;
    case V_GLUEEL: t = mk_term(T_GLUEEL, NULL, NULL, NULL, NULL); qpush(depth, v->a, &t->a); qpush(depth, v->b, &t->b); qpush(depth, v->c, &t->c); break;
    case V_SYS:
        t = mk(T_SYS); t->nbr = v->nbr; t->br = xalloc((v->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < v->nbr; i++) { qpush(depth, v->br[i].phi, &t->br[i].face); qpush(depth, v->br[i].v, &t->br[i].body); }
        break;
    case V_NUM: return mk_num(v->n, quote_level(depth, v->lvl), v->num);
    case V_NEU: case V_DATA: case V_CON: {
        Term *h;
        if (v->k == V_DATA) h = mk_ref_l(T_DATA, v->n, quote_level(depth, v->lvl));
        else if (v->k == V_CON) h = mk_ref_l(T_CON, v->n, quote_level(depth, v->lvl));
        else if (v->h == H_ELIM) h = mk_ref_l(T_ELIM, v->n, quote_level(depth, v->lvl));
        else if (v->h == H_TRANSP) { h = mk_term(T_TRANSP, NULL, NULL, NULL, NULL); qpush(depth, v->a, &h->a); qpush(depth, v->b, &h->b); qpush(depth, v->c, &h->c); }
        else if (v->h == H_HCOMP) { h = mk_term(T_HCOMP, NULL, NULL, NULL, NULL); qpush(depth, v->a, &h->a); qpush(depth, v->b, &h->b); qpush(depth, v->c, &h->c); qpush(depth, v->dom, &h->d); }
        else if (v->h == H_OUTS) { h = mk_term(T_OUTS, NULL, NULL, NULL, NULL); qpush(depth, v->a, &h->a); qpush(depth, v->b, &h->b); qpush(depth, v->c, &h->c); qpush(depth, v->dom, &h->d); }
        else if (v->h == H_UNGLUE) { h = mk_term(T_UNGLUE, NULL, NULL, NULL, NULL); qpush(depth, v->dom, &h->a); qpush(depth, v->a, &h->b); qpush(depth, v->b, &h->c); qpush(depth, v->c, &h->d); }
        else if (v->h == H_META) { h = mk_term(T_META, NULL, NULL, NULL, NULL); h->n = v->n; }
        else if (v->h == H_DEF) h = mk_ref_l(T_DEF, v->n, quote_level(depth, v->lvl));
        else h = mk_var(depth - 1 - v->n);
        for (int i = 0; i < v->args.n; i++) {
            Arg *a = &v->args.a[i];
            if (a->proj) h = mk_term(a->proj == 1 ? T_FST : T_SND, h, NULL, NULL, NULL);
            else if (a->papp) { h = mk_term(T_PAPP, h, NULL, NULL, NULL); qpush(depth, a->v, &h->b); qpush(depth, a->x, &h->c); qpush(depth, a->y, &h->d); }
            else { h = mk_app(h, NULL, a->irr); qpush(depth, a->v, &h->b); }
        }
        t = h;
        break;
    }
    default: return NULL;
    }
    if (nqs > from) for (size_t i = from, j = nqs - 1; i < j; i++, j--) { QTask x = qs[i]; qs[i] = qs[j]; qs[j] = x; }
    return t;
}
Term *quote(int depth, Val *v) {
    Term *root = NULL; size_t base = nqs;
    qpush(depth, v, &root);
    while (nqs > base) { QTask q = qs[--nqs]; *q.dst = quote_node(q.depth, q.v); }
    return root;
}
int val_mentions_ivar(int depth, Val *v, int level) { return term_mentions_var(quote(depth, v), depth - 1 - level); }

/* ---- conversion ----
   An explicit machine, not C recursion: the goals left to prove sit on a heap stack in the order the recursive
   definition visited them (depth first, left to right), so a comparison's depth is bounded by memory alone
   (Order_Lev_EezottIterative). Conversion is a conjunction of goals except at three speculative points - the same
   definition's spines, the same deferred elimination's spines, the same meta's spines - where a failure is recovered:
   a frame there holds the rollback marks, the goal stack's height, and the fallback (unfold both, force both,
   postpone). A failure rolls back to the innermost frame and resumes its fallback; with none left, the whole
   comparison fails and is rolled back (conversion is transactional). A conversion nested inside a step (unify_meta,
   eval) runs its own machine above the outer one's goals and leaves the stacks as it found them. */
typedef enum { G_PLAIN, G_PROJ2, G_CLO, G_FACE, G_SPEC_END, G_RESUME } GKind;
typedef enum { FB_DEF, FB_ELIM, FB_META } FbKind;
typedef struct { GKind k; int depth; Val *a, *b; int isi; FbKind fb; Face face; } Goal;
typedef struct { LMark lm; MMark mm; int height; FbKind fb; int depth; Val *a, *b; } Spec;
static Stack gst = { NULL, 0, 0, sizeof(Goal) }, sst = { NULL, 0, 0, sizeof(Spec) };   /* Stacks of the memory layer */
#define gs ((Goal *)gst.p)
#define ngs (gst.n)
#define ss ((Spec *)sst.p)
#define nss (sst.n)
static void gpush(Goal g) { STACK_PUSH(&gst, Goal, g); }
static void gpush2(GKind k, int depth, Val *a, Val *b) { Goal g = {0}; g.k = k; g.depth = depth; g.a = a; g.b = b; gpush(g); }
/* a speculative block: the marks were taken before anything it may undo; its goals go above the end marker */
static void spec_open(LMark lm, MMark mm, FbKind fb, int depth, Val *a, Val *b) {
    Spec s = { lm, mm, (int)ngs, fb, depth, a, b }; STACK_PUSH(&sst, Spec, s);
    gpush2(G_SPEC_END, depth, NULL, NULL);
}
/* a spine's argument pairs, left to right: path and plain application to an interval coincide; the argument of an
   irrelevant binder is not compared. 0 refuted, 2 pushed. */
static int push_spine(int depth, VList *a, VList *b) {
    if (a->n != b->n) return 0;
    for (int i = 0; i < a->n; i++) if (a->a[i].proj != b->a[i].proj) return 0;
    for (int i = a->n - 1; i >= 0; i--) {
        if (a->a[i].proj) continue;
        if ((a->a[i].irr & 2) && (b->a[i].irr & 2)) continue;
        gpush2(G_PLAIN, depth, a->a[i].v, b->a[i].v);
    }
    return 2;
}
/* partial elements agree on every face of their (common) support */
static int push_sys(int depth, Val *a, Val *b) {
    Val *s = a->k == V_SYS ? a : b;
    IVal phi = iv_zero();
    for (int i = 0; i < s->nbr; i++) phi = iv_or(phi, s->br[i].phi->iv);
    Face *fs; int nf = iv_faces(phi, &fs);
    for (int i = nf - 1; i >= 0; i--) { Goal g = {0}; g.k = G_FACE; g.depth = depth; g.a = a; g.b = b; g.face = fs[i]; gpush(g); }
    return 2;
}
/* the levels of two occurrences of a global agree (only polymorphic globals take one) */
static int lvl_conv(TKind k, int id, LVal a, LVal b) { return !ref_poly(k, id) || lv_enforce_eq(a, b) == 1; }
/* one step on a goal: 1 proved, 0 refuted, 2 its subgoals pushed. skip: the head phase is done (a fallback found
   nothing left to unfold) */
static int conv_step(int depth, Val *a, Val *b, int skip) {
    a = fmeta(a); b = fmeta(b);
    /* definition applications stay rigid: the same definition compares by spine congruence, and the spine's arguments
       at .() binders (irr bit 2) are skipped - proofs differing only there are equal by construction (compareIrrelevant
       in Agda; the H_DEF plan). Different definitions (or a rigid against something else): unfold and continue. */
    while (!skip) {
        int ad = a->k == V_NEU && a->h == H_DEF, bd = b->k == V_NEU && b->h == H_DEF;
        int ae = a->k == V_NEU && a->h == H_ELIM && a->defer, be = b->k == V_NEU && b->h == H_ELIM && b->defer;
        /* a metavariable is solved by the other side as written - a rigid definition application, a deferred
           elimination - so the solution is the term the user wrote (M19). Only when that postpones for a variable
           out of the spine's scope is the other side unfolded and the constraint tried again: a definition may
           drop the variable, and that solution was found before. */
        { int am = a->k == V_NEU && a->h == H_META, bm = b->k == V_NEU && b->h == H_META;
          if ((am || bm) && !(am && bm)) {
              Val *o = am ? b : a, *mv = am ? a : b;
              int r = unify_meta(depth, mv, o);
              if (r == 1) return 1;
              /* r is 0 (the meta occurs in the side as written) or 3 (postponed for a variable outside the spine):
                 either may vanish when that side is unfolded - a definition may drop the argument or the variable -
                 so it is unfolded one step and the constraint tried again. Nothing left to unfold: an occurrence
                 is the failure it is, a scope postponement stays. */
              Val *u = o;
              if (o->k == V_NEU && o->h == H_DEF) u = fmeta(unfold_def(o));
              else if (o->k == V_NEU && o->h == H_ELIM && o->defer) u = fmeta(elim_force(o));
              if (u == o) return r == 3;
              if (r == 3) meta_drop_last_post();
              if (am) b = u; else a = u;
              continue;
          }
          if (am && bm) break; }
        if (ad && bd) {
            /* the fast path: the same definition, spines convertible (the .() arguments skipped) - equal by congruence;
               speculative: on failure everything it did is rolled back and both sides unfold (FB_DEF) */
            if (a->n == b->n && a->args.n == b->args.n) {
                LMark lm = lstore_mark(); MMark mm = meta_mark();
                if (lvl_conv(T_DEF, a->n, a->lvl, b->lvl)) { spec_open(lm, mm, FB_DEF, depth, a, b); return push_spine(depth, &a->args, &b->args); }
                lstore_rollback(lm); meta_rollback(mm);
            }
            /* Two different definitions: unfold ONE side, the later-declared one first (Coq's and Agda's definition
               height). A wrapper's body usually reaches the other definition's own head, and the congruence fast path
               then settles it; unfolding both at once turns the other side into its evaluated body - an elimination on
               a literal fuel, say - and the comparison walks that body's closures (Bug_Eezott_ConvUnfoldsBothSides).
               A native's guard neutral unfolds to itself: it is rigid, and two of them differ by their spines. */
            Val *ua, *ub;
            if (a->n != b->n) {
                if (a->n > b->n) { ua = fmeta(unfold_def(a)); if (ua != a) { a = ua; continue; } ub = fmeta(unfold_def(b)); if (ub != b) { b = ub; continue; } }
                else { ub = fmeta(unfold_def(b)); if (ub != b) { b = ub; continue; } ua = fmeta(unfold_def(a)); if (ua != a) { a = ua; continue; } }
                break;
            }
            ua = fmeta(unfold_def(a)); ub = fmeta(unfold_def(b));
            if (ua == a && ub == b) break;
            a = ua; b = ub; continue;
        }
        if (ad) { Val *u = fmeta(unfold_def(a)); if (u != a) { a = u; continue; } }
        if (bd) { Val *u = fmeta(unfold_def(b)); if (u != b) { b = u; continue; } }
        /* deferred eliminations: the same one by spine congruence (speculative, FB_ELIM), else reduced (a stuck one
           drops its flag) */
        if (ae && be) {
            if (a->n == b->n && a->args.n == b->args.n) {
                LMark lm = lstore_mark(); MMark mm = meta_mark();
                if (lvl_conv(T_ELIM, a->n, a->lvl, b->lvl)) { spec_open(lm, mm, FB_ELIM, depth, a, b); return push_spine(depth, &a->args, &b->args); }
                lstore_rollback(lm); meta_rollback(mm);
            }
            a = fmeta(elim_force(a)); b = fmeta(elim_force(b)); continue;
        }
        if (ae) { a = fmeta(elim_force(a)); continue; }
        if (be) { b = fmeta(elim_force(b)); continue; }
        break;
    }
    /* a level variable is a level value in the context and a neutral variable under a binder opened by conversion */
    if (a->k == V_L && b->k == V_NEU && b->h == H_VAR && b->args.n == 0) return lv_enforce_eq(a->lvl, lv_var(b->n)) == 1;
    if (b->k == V_L && a->k == V_NEU && a->h == H_VAR && a->args.n == 0) return lv_enforce_eq(b->lvl, lv_var(a->n)) == 1;
    if (a == b) return 1;
    {   /* a meta: solved by pattern unification, or the constraint is postponed (the same meta: its spines,
           speculatively - on failure the constraint is postponed, FB_META) */
        int am = a->k == V_NEU && a->h == H_META, bm = b->k == V_NEU && b->h == H_META;
        if (am && bm && a->n == b->n) {
            LMark lm = lstore_mark(); MMark mm = meta_mark();
            spec_open(lm, mm, FB_META, depth, a, b);
            return push_spine(depth, &a->args, &b->args);
        }
        if (am) return unify_meta(depth, a, b);
        if (bm) return unify_meta(depth, b, a);
    }
    /* literals (M15): equal numbers; against constructors, one constructor at a time */
    if (a->k == V_NUM && b->k == V_NUM) return a->n == b->n && lvl_conv(T_DATA, a->n, a->lvl, b->lvl) && bn_cmp(a->num, b->num) == 0;
    if (a->k == V_NUM && b->k == V_CON) a = num_view(a);
    if (b->k == V_NUM && a->k == V_CON) b = num_view(b);
    if (a->k == V_SYS || b->k == V_SYS) return push_sys(depth, a, b);
    if (a->k == V_LAM || b->k == V_LAM) {          /* eta */
        int isi = (a->k == V_LAM ? a->isi : b->isi);
        Val *x = isi ? vivar(depth) : vvar(depth);
        /* a neutral applied to an interval is the same application whether it was formed as a path or as a function of I */
        Val *fa = a->k == V_LAM ? inst(&a->clo, x) : vapp(a, x, 0);
        Val *fb = b->k == V_LAM ? inst(&b->clo, x) : vapp(b, x, 0);
        gpush2(G_PLAIN, depth + 1, fa, fb); return 2;
    }
    if (a->k == V_IRR || b->k == V_IRR) die("internal: an elided irrelevant value reached conversion");
    if (a->k == V_PAIR || b->k == V_PAIR) {   /* eta; an irrelevant second component is not compared */
        int irr = (a->k == V_PAIR && a->irr) || (b->k == V_PAIR && b->irr);
        if (!irr) gpush2(G_PROJ2, depth, a, b);
        gpush2(G_PLAIN, depth, vproj(a, 1), vproj(b, 1)); return 2;
    }
    if (a->k != b->k) return 0;
    switch (a->k) {
    case V_U: return a->pre == b->pre && lv_enforce_eq(a->lvl, b->lvl) == 1;
    case V_L: return lv_enforce_eq(a->lvl, b->lvl) == 1;
    case V_LEVEL: return 1;
    case V_SIGMA: {
        if (a->irr != b->irr) return 0;
        Goal g = {0}; g.k = G_CLO; g.depth = depth; g.a = a; g.b = b; g.isi = 0; gpush(g);
        gpush2(G_PLAIN, depth, a->dom, b->dom); return 2;
    }
    case V_INTERVAL: return 1;
    case V_I: return iv_eq(a->iv, b->iv);
    case V_PI: {
        Goal g = {0}; g.k = G_CLO; g.depth = depth; g.a = a; g.b = b; g.isi = a->isi; gpush(g);
        gpush2(G_PLAIN, depth, a->dom, b->dom); return 2;
    }
    case V_PATHP: case V_SUB: case V_GLUE:
        gpush2(G_PLAIN, depth, a->c, b->c); gpush2(G_PLAIN, depth, a->b, b->b); gpush2(G_PLAIN, depth, a->a, b->a); return 2;
    case V_PARTIAL: gpush2(G_PLAIN, depth, a->b, b->b); gpush2(G_PLAIN, depth, a->a, b->a); return 2;
    case V_INS: gpush2(G_PLAIN, depth, a->a, b->a); return 2;
    case V_GLUEEL: gpush2(G_PLAIN, depth, a->a, b->a); gpush2(G_PLAIN, depth, a->b, b->b); return 2;
    case V_NEU:
        if (a->h != b->h) return 0;
        if (a->h != H_TRANSP && a->h != H_HCOMP && a->h != H_OUTS && a->h != H_UNGLUE
            && (a->n != b->n || (a->h != H_VAR && !lvl_conv(T_ELIM, a->n, a->lvl, b->lvl)))) return 0;   /* a variable's n is its level, not a global id */
        if (!push_spine(depth, &a->args, &b->args)) return 0;   /* the spine after the head's own parts */
        if (a->h == H_TRANSP) { gpush2(G_PLAIN, depth, a->c, b->c); gpush2(G_PLAIN, depth, a->b, b->b); gpush2(G_PLAIN, depth, a->a, b->a); }
        else if (a->h == H_HCOMP) { gpush2(G_PLAIN, depth, a->dom, b->dom); gpush2(G_PLAIN, depth, a->c, b->c); gpush2(G_PLAIN, depth, a->b, b->b); gpush2(G_PLAIN, depth, a->a, b->a); }
        else if (a->h == H_OUTS || a->h == H_UNGLUE) gpush2(G_PLAIN, depth, a->dom, b->dom);
        return 2;
    case V_DATA: case V_CON:
        if (!(a->n == b->n && lvl_conv(a->k == V_DATA ? T_DATA : T_CON, a->n, a->lvl, b->lvl))) return 0;
        return push_spine(depth, &a->args, &b->args);
    default: return 0;
    }
}
/* a speculative block failed (its marks already rolled back): its fallback */
static int conv_resume(Goal g) {
    switch (g.fb) {
    case FB_DEF: {
        Val *ua = fmeta(unfold_def(g.a)), *ub = fmeta(unfold_def(g.b));
        if (ua == g.a && ub == g.b) return conv_step(g.depth, g.a, g.b, 1);
        return conv_step(g.depth, ua, ub, 0);
    }
    case FB_ELIM: return conv_step(g.depth, fmeta(elim_force(g.a)), fmeta(elim_force(g.b)), 0);
    case FB_META: meta_postpone(g.depth, g.a, g.b); return 1;
    }
    return 0;
}
static int conv_fail_logged;
/* conversion is transactional: level constraints and meta solutions added by a comparison that fails are rolled back */
int conv(int depth, Val *a, Val *b) {
    LMark m = lstore_mark(); MMark mm = meta_mark();
    size_t gbase = ngs, sbase = nss;
    gpush2(G_PLAIN, depth, a, b);
    while (ngs > gbase) {
        Goal g = gs[--ngs];
        int r = 0;
        switch (g.k) {
        case G_SPEC_END: nss--; continue;   /* the speculative spines all held: the goal that opened the block is proved */
        case G_PLAIN: r = conv_step(g.depth, g.a, g.b, 0); break;
        case G_PROJ2: r = conv_step(g.depth, vproj(g.a, 2), vproj(g.b, 2), 0); break;
        case G_CLO: { Val *x = g.isi ? vivar(g.depth) : vvar(g.depth); r = conv_step(g.depth + 1, inst(&g.a->clo, x), inst(&g.b->clo, x), 0); break; }
        case G_FACE: { Val *x = vsys_at(g.a, &g.face), *y = vsys_at(g.b, &g.face); r = x && y ? conv_step(g.depth, x, y, 0) : 0; break; }
        case G_RESUME: r = conv_resume(g); break;
        }
        if (r) continue;
        if (conv_fail_logged < 20 && getenv("EEZOTT_CONV_TRACE") && (g.k == G_PLAIN)) {
            conv_fail_logged++;
            fprintf(stderr, "[conv] #%d depth %d goals %zu: ", conv_fail_logged, g.depth, ngs - gbase);
            const char *nm[2048] = {0};
            term_print(stderr, quote(0, g.a), nm, 0); fputs("   !=   ", stderr);
            term_print(stderr, quote(0, g.b), nm, 0); fputc('\n', stderr);
            if ((g.a->k == V_I || g.b->k == V_I) && getenv("EEZOTT_CONV_TRAP")) __builtin_trap();
        }
        if (nss > sbase) {   /* recovered: roll the innermost speculative block back and take its fallback */
            Spec s = ss[--nss];
            lstore_rollback(s.lm); meta_rollback(s.mm); ngs = s.height;
            Goal rg = {0}; rg.k = G_RESUME; rg.fb = s.fb; rg.depth = s.depth; rg.a = s.a; rg.b = s.b; gpush(rg);
            continue;
        }
        ngs = gbase; nss = sbase; lstore_rollback(m); meta_rollback(mm);
        return 0;
    }
    return 1;
}
