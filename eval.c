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
void die_resource(const char *fmt, ...) {
    va_list ap;
    fflush(stdout);
    fputs("eezott: resource limit: ", stderr);
    va_start(ap, fmt); vfprintf(stderr, fmt, ap); va_end(ap);
    fputc('\n', stderr);
    exit(70);
}

/* A memo entry stays valid across metas generations iff nothing inside it was blocked on an unsolved meta: resolving one
   can resume a reduction the entry took as neutral. A missed entry is merely slow, so this is set conservatively -
   every place that hands back a neutral where a decision was possible marks it, meta or not. */
static int meta_blocked;
static u64 alloc_total, alloc_limit;
void *xalloc(size_t n) {
    if (!alloc_limit) {   /* off unless the harness asks: the budget is the harness's cap, not the theory's */
        const char *e = getenv("EEZOTT_MAX_ALLOC");
        alloc_limit = e ? strtoull(e, NULL, 0) : (u64)-1;
    }
    alloc_total += n ? n : 1;
    if (alloc_total > alloc_limit)
        die_resource("allocated over %llu bytes (EEZOTT_MAX_ALLOC)", (unsigned long long)alloc_limit);
    void *p = calloc(1, n ? n : 1);
    if (!p) die_resource("out of memory");
    return p;
}
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
Val *def_at(int id, LVal L) {
    Def *d = &defs[id]; int n;
    if (!d->poly) return d->vval;
    if (!lv_is_const(L, &n)) {
        static LMemoList *dm; static int ndm;
        LMemoList *ml = memo_for(&dm, &ndm, id); Val *r = lmemo_get(ml, L);
        if (!r) { r = eval(NULL, subst_hidden(d->val, L)); lmemo_put(ml, L, r); }
        return r;
    }
    if (n >= d->nat) {
        int m = n + 4; Val **nv = xalloc(m * sizeof(Val *)), **nt = xalloc(m * sizeof(Val *));
        for (int i = 0; i < d->nat; i++) { nv[i] = d->vval_at[i]; nt[i] = d->vty_at[i]; }
        d->vval_at = nv; d->vty_at = nt; d->nat = m;
    }
    if (!d->vval_at[n]) d->vval_at[n] = eval(NULL, subst_hidden(d->val, L));
    return d->vval_at[n];
}
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
static void tp(FILE *f, Term *t, const char **names, int depth, int prec);
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
static void ref_lvl_tp(FILE *f, Term *t, const char **names, int depth) {
    int hn;
    if (!t->a) return;
    if (t->a->k == T_LVAL && lv_is_hidden_plus(t->a->lvl, &hn)) { if (hn) fprintf(f, "^%d", hn); return; }
    fputs("^{", f); tp(f, t->a, names, depth, 0); fputc('}', f);
}
static void tp(FILE *f, Term *t, const char **names, int depth, int prec) {
    unsigned long long num;
    if ((t->k == T_APP || t->k == T_CON) && numeral_of(t, &num)) { fprintf(f, "%llu", num); return; }
    switch (t->k) {
    case T_VAR: {
        int lvl = depth - 1 - t->n;
        if (lvl >= 0 && lvl < depth && names[lvl]) fprintf(f, "%s", names[lvl]); else fprintf(f, "#%d", t->n);
        break; }
    case T_U: {
        int hn;
        fputs(t->pre ? "Pre" : "U", f);
        if (t->a && t->a->k == T_LVAL && lv_is_hidden_plus(t->a->lvl, &hn)) { if (hn) fprintf(f, " %d", hn); }   /* the hidden level + n reads as U n */
        else if (t->a) { fputs(" {", f); tp(f, t->a, names, depth, 0); fputc('}', f); }
        else if (t->n) fprintf(f, " %d", t->n);
        break; }
    case T_LEVEL: fputs("Level", f); break;
    case T_LZERO: fprintf(f, "%d", t->n); break;
    case T_LMETA: fprintf(f, "?%d", t->n); break;
    case T_META: fprintf(f, "?%d", t->n); break;
    case T_LSUC: {
        int atom = t->a->k == T_VAR || t->a->k == T_LZERO;
        if (prec > 1) fputc('(', f);
        for (int i = 0; i < t->n; i++) fputs(i + 1 < t->n || !atom ? "lsuc (" : "lsuc ", f);
        tp(f, t->a, names, depth, 0);
        for (int i = 0; i < t->n; i++) if (i + 1 < t->n || !atom) fputc(')', f);
        if (prec > 1) fputc(')', f);
        break; }
    case T_LMAX: if (prec > 0) fputc('(', f); fputs("lmax ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); if (prec > 0) fputc(')', f); break;
    case T_DEF: fprintf(f, "%s", defs[t->n].name); ref_lvl_tp(f, t, names, depth); break;
    case T_DATA: fprintf(f, "%s", datas[t->n].name); ref_lvl_tp(f, t, names, depth); break;
    case T_CON: fprintf(f, "%s", cons[t->n].name); ref_lvl_tp(f, t, names, depth); break;
    case T_NUM: { char *s = bn_to_dec(t->num); fputs(s, f); free(s); break; }
    case T_IRR: fputc('.', f); break;
    case T_ELIM: fprintf(f, "elim %s", datas[t->n].name); ref_lvl_tp(f, t, names, depth); break;
    case T_LVAL: lv_tp(f, t->lvl, names, depth, prec); break;
    case T_INTERVAL: fputs("I", f); break;
    case T_I0: fputs("i0", f); break;
    case T_I1: fputs("i1", f); break;
    case T_INEG: fputs("~ ", f); tp(f, t->a, names, depth, 3); break;
    case T_IAND: if (prec > 0) fputc('(', f); tp(f, t->a, names, depth, 1); fputs(" /\\ ", f); tp(f, t->b, names, depth, 1); if (prec > 0) fputc(')', f); break;
    case T_IOR:  if (prec > 0) fputc('(', f); tp(f, t->a, names, depth, 1); fputs(" \\/ ", f); tp(f, t->b, names, depth, 1); if (prec > 0) fputc(')', f); break;
    case T_PI: {
        if (prec > 0) fputc('(', f);
        const char *nm = t->name && strcmp(t->name, "_") ? t->name : NULL;
        if (nm) { fprintf(f, t->imp ? "{%s : " : (t->irr & 2) ? ".(%s : " : "(%s : ", nm); tp(f, t->a, names, depth, 0); fputs(t->imp ? "} -> " : ") -> ", f); }
        else { tp(f, t->a, names, depth, 1); fprintf(f, " -> "); }
        names[depth] = nm ? nm : "_"; tp(f, t->b, names, depth + 1, 0);
        if (prec > 0) fputc(')', f);
        break; }
    case T_SIGMA: {
        if (prec > 1) fputc('(', f);
        fprintf(f, "Sigma "); tp(f, t->a, names, depth, 2); fprintf(f, " (\\%s -> ", t->name ? t->name : "_");
        names[depth] = t->name ? t->name : "_"; tp(f, t->b, names, depth + 1, 0); fputc(')', f);
        if (prec > 1) fputc(')', f);
        break; }
    case T_PAIR: fputc('(', f); tp(f, t->a, names, depth, 0); fputs(" , ", f); tp(f, t->b, names, depth, 0); fputc(')', f); break;
    case T_FST: if (prec > 1) fputc('(', f); fputs("fst ", f); tp(f, t->a, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_GLUE:
        if (prec > 1) fputc('(', f);
        fputs("Glue ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); fputc(' ', f); tp(f, t->c, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_GLUEEL: if (prec > 1) fputc('(', f); fputs("glue ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_UNGLUE: if (prec > 1) fputc('(', f); fputs("unglue ", f); tp(f, t->a, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_SND: if (prec > 1) fputc('(', f); fputs("snd ", f); tp(f, t->a, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_LAM: {
        if (prec > 0) fputc('(', f);
        fprintf(f, t->imp ? "\\{%s} -> " : "\\%s -> ", t->name); names[depth] = t->name; tp(f, t->a, names, depth + 1, 0);
        if (prec > 0) fputc(')', f);
        break; }
    case T_APP: case T_PAPP:
        if (prec > 1) fputc('(', f);
        tp(f, t->a, names, depth, 1); fputc(' ', f); tp(f, t->b, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_LET:
        if (prec > 0) fputc('(', f);
        fprintf(f, "let %s : ", t->name); tp(f, t->a, names, depth, 0); fprintf(f, " := "); tp(f, t->b, names, depth, 0);
        fprintf(f, " in "); names[depth] = t->name; tp(f, t->c, names, depth + 1, 0);
        if (prec > 0) fputc(')', f);
        break;
    case T_PATHP:
        if (prec > 1) fputc('(', f);
        fputs("PathP ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); fputc(' ', f); tp(f, t->c, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_PARTIAL:
        if (prec > 1) fputc('(', f);
        fputs("Partial ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_TRANSP:
        if (prec > 1) fputc('(', f);
        fputs("transp ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); fputc(' ', f); tp(f, t->c, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_HCOMP:
        if (prec > 1) fputc('(', f);
        fputs("hcomp ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); fputc(' ', f);
        tp(f, t->c, names, depth, 2); fputc(' ', f); tp(f, t->d, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_SUB:
        if (prec > 1) fputc('(', f);
        fputs("Sub ", f); tp(f, t->a, names, depth, 2); fputc(' ', f); tp(f, t->b, names, depth, 2); fputc(' ', f); tp(f, t->c, names, depth, 2);
        if (prec > 1) fputc(')', f);
        break;
    case T_INS: if (prec > 1) fputc('(', f); fputs("inS ", f); tp(f, t->a, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_OUTS: if (prec > 1) fputc('(', f); fputs("outS ", f); tp(f, t->d, names, depth, 2); if (prec > 1) fputc(')', f); break;
    case T_SYS:
        fputs("[ ", f);
        for (int i = 0; i < t->nbr; i++) { if (i) fputs(" | ", f); tp(f, t->br[i].face, names, depth, 0); fputs(" -> ", f); tp(f, t->br[i].body, names, depth, 0); }
        fputs(" ]", f);
        break;
    }
}
void term_print(FILE *f, Term *t, const char **names, int depth) { tp(f, t, names, depth, 0); }

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
Val *inst(Clo *c, Val *v) {
    /* One-entry application memo (the memoization pass): a closure applied to the same value again is the same value,
       and branch bodies do apply the same closure to the same value repeatedly - baddGo's column uses its induction
       hypothesis three times, and each application re-ran the whole recursive fold, which made the fold's cost
       3^columns (Finding_Eezott_EvalNoSharing_2026_09_14). The metas version guards it: a meta solved in between can
       resume a reduction that the first application took as neutral. */
    if (c->ires && c->iarg == v && (c->imv == metas_version || c->istable)) return c->ires;
    int save = meta_blocked; meta_blocked = 0;
    Val *r = c->fn ? c->fn(c->data, v) : eval(env_push(c->env, v), c->t);
    c->iarg = v; c->ires = r; c->imv = metas_version; c->istable = !meta_blocked;
    meta_blocked |= save;
    return r;
}
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
    case 10: {   /* the modular inverse x ^ (y - 2) mod y: Fermat, one exponent and one division */
        Bn *two = bn_from_u64(2), *e = bn_monus(b, two), *q, *r2;
        bn_divmod(bn_pow(a, e), b, &q, &r2);
        return r2;
    }
    }
    die("internal: unknown native %d", code); return NULL;
}
typedef struct { int code, d; Val *fallback, *arg1; } NatNative;
static Val *natfn(void *data, Val *arg) {
    NatNative *nn = data;
    if (!nn->arg1) { NatNative *m = xalloc(sizeof *m); *m = *nn; m->arg1 = arg; return vlam_native("n", natfn, m); }
    Val *a = force(nn->arg1), *b = force(arg);
    if (a->k == V_NUM && b->k == V_NUM && a->n == nn->d && b->n == nn->d) return vnum(nn->d, a->lvl, nat_op(nn->code, a->num, b->num));
    return vapp(vapp(nn->fallback, nn->arg1, 0), arg, 0);
}
Val *native_wrapper(int code, int d, Val *fallback) {
    NatNative *nn = xalloc(sizeof *nn); nn->code = code; nn->d = d; nn->fallback = fallback; nn->arg1 = NULL;
    return vlam_native("m", natfn, nn);
}
static Val *elim_apply_list(int data, VList *args);

/* ---- induction hypotheses (native closure N_IH) ----
   cap = base (params, motive, methods), tele (params, previous args), ys, aj; i1=data i2=con i3=j; ys count = cap.n - nb - nt - 1 */
static Val *ih_apply(Native *c, Val *y) {
    int nb = datas[c->i1].nparams + datas[c->i1].nblock + block_ncons(c->i1);
    Con *C = con_at(c->i2, c->l); int j = c->i3; int nt = datas[c->i1].nparams + j;
    ConArg *ca = &C->args[j];
    Native *d = xalloc(sizeof *d); *d = *c; d->cap = vl_copy(&c->cap);
    /* insert y before the trailing aj */
    Arg aj = d->cap.a[d->cap.n - 1]; d->cap.n--; vl_push(&d->cap, y, 0); vl_push_arg(&d->cap, aj);
    int ny = d->cap.n - nb - nt - 1;
    if (ny < ca->npi) { Val *v = mkval(V_LAM); v->clo.fn = nfn; v->clo.data = d; v->name = "y"; return v; }
    Env *e = NULL; for (int i = 0; i < nt; i++) e = env_push(e, d->cap.a[nb + i].v);
    for (int i = 0; i < ny; i++) e = env_push(e, d->cap.a[nb + nt + i].v);
    VList args = {0};
    for (int i = 0; i < nb; i++) vl_push(&args, d->cap.a[i].v, prefix_irr(c->i1, i));
    for (int i = 0; i < ca->nidx; i++) vl_push(&args, eval(e, ca->idx[i]), 1);
    Val *t = d->cap.a[d->cap.n - 1].v; for (int i = 0; i < ny; i++) t = vapp(t, d->cap.a[nb + nt + i].v, 0);
    vl_push(&args, t, 0);
    return elim_apply_list(c->i1, &args);
}

/* the motive of member `data` applied to the indices and, where an index ranges over a member, to its image: that member's
   elimination of it with the same prefix (M11b) */
static Val *motive_applied(int data, VList *pre, Val **idx) {
    Data *D = &datas[data]; int np = D->nparams, nb = D->nblock, K = block_ncons(data);
    Val *P = pre->a[np + D->bpos].v;
    for (int j = 0; j < D->nidx; j++) {
        P = vapp(P, idx[j], 1);
        if (D->idxrec[j] >= 0) {
            VList a2 = {0}; for (int i = 0; i < np + nb + K; i++) vl_push(&a2, pre->a[i].v, prefix_irr(data, i));
            vl_push(&a2, idx[j], 0);
            P = vapp(P, elim_apply_list(D->idxrec[j], &a2), 0);
        }
    }
    return P;
}
/* iota: the eliminator's full spine ends in a constructor */
static int elim_data_cur;
static Val *elim_of_branch(Val *b, void *data);
static Val *vsys(VBranch *br, int n);
static Val *vsys_map(Val *sys, Val *(*fn)(Val *, void *), void *data);
/* The literal-elimination tripwire. A method that uses its induction hypothesis walks the literal a step at a
   time, so a walk over a machine-sized literal is work proportional to the literal - 1e19 steps at the word
   bounds. What it must count is NESTING: a walk nests (the branch forces its induction hypothesis inside this
   call), while a program that merely uses many literals does not. Counted as a running total instead, the
   tripwire fires on the 66th innocent use of a literal anywhere in the run, and names an innocent walker.
   The chunk rule below keeps almost every walk from starting at all; the tripwire stays as the backstop for
   the methods whose term cannot be inspected (M16b A2). */
static int elim_num_depth;
static int elim_num_big;   /* the elimination under way is on a machine-sized literal: one successor of it is a word of steps */
static Val *elim_reduce_go(int data, VList *args);
static Val *elim_reduce(int data, VList *args) {
    Val *target = force(args->a[args->n - 1].v);
    if (target->k != V_NUM) return elim_reduce_go(data, args);
    int bits = bn_bitlen(target->num);
    if (bits > 40 && elim_num_depth > 64) {
        char *dec = bn_to_dec(target->num);   /* name the literal itself: the bits alone do not say which bound was walked */
        if (strlen(dec) > 40) { dec[40] = 0; }
        die_resource("elimination of %s recursed %d deep on the literal %s in %s: the induction hypothesis is used, so this is work proportional to the literal",
                     datas[data].name, elim_num_depth, dec, cur_decl_name ? cur_decl_name : "the top level");
    }
    elim_num_depth++;
    int save_big = elim_num_big; elim_num_big = bits > 40;
    Val *r = elim_reduce_go(data, args);
    elim_num_big = save_big;
    elim_num_depth--;
    return r;
}
static Val *elim_reduce_go(int data, VList *args) {
    Data *D = data_at(data, elim_lvl); elim_data_cur = data;
    int np = D->nparams, nb = D->nblock, K = block_ncons(data);
    Val *target = force(args->a[args->n - 1].v);   /* a rigid definition application unfolds for the elimination */
    if (target->k == V_NUM) target = num_view(target);   /* a literal eliminates as one constructor */
    if (target->k != V_CON) { meta_blocked = 1; return NULL; }
    Con *c = con_at(target->n, target->lvl);
    if (c->data != data || target->args.n != np + c->nargs + c->nint) { meta_blocked = 1; return NULL; }
    Val *res = args->a[np + nb + c->bord].v;
    for (int j = 0; j < c->nargs; j++) res = vapp(res, target->args.a[np + j].v, c->args[j].irr);
    for (int j = 0; j < c->nargs; j++) {
        if (c->args[j].isrecpath) {   /* the induction hypothesis over a path argument is the dependent path  k. elim .. idx (p k) */
            Native *ih = xalloc(sizeof *ih); ih->code = N_ELIM_PATH_IH; ih->i1 = c->args[j].rec;
            for (int i = 0; i < np + nb + K; i++) vl_push(&ih->cap, args->a[i].v, prefix_irr(data, i));
            Env *e = NULL; for (int i = 0; i < np + j; i++) e = env_push(e, target->args.a[i].v);
            for (int q = 0; q < c->args[j].nidx; q++) vl_push(&ih->cap, eval(e, c->args[j].idx[q]), 1);
            vl_push(&ih->cap, target->args.a[np + j].v, 0);
            vl_push(&ih->cap, eval(e, c->args[j].px), 0); vl_push(&ih->cap, eval(e, c->args[j].py), 0);
            Val *ihv = mkval(V_LAM); ihv->clo.fn = nfn; ihv->clo.data = ih; ihv->name = "k"; ihv->isi = 1;
            res = vapp(res, ihv, 0);
            continue;
        }
        if (!c->args[j].isrec) continue;
        /* a method that does not mention its induction hypothesis does not get one computed: a case analysis on a literal
           (isZero, pred, if01 ..) would otherwise recurse down to zero (M16a) */
        if (c->args[j].npi == 0 && res->k == V_LAM && !res->clo.fn && !term_mentions_var(res->clo.t, 0)) { res = vapp(res, target->args.a[np + j].v, 0); continue; }
        /* A method that does mention it walks the literal one successor per step, and one successor of a machine-sized
           literal is a word of steps: no chunk of a fold is the value its step expects, so there is no walk to make
           here. The elimination stands as a neutral - the same term, just not unfolded - which is what the method's
           own use of it would compute anyway (M16b A2). */
        if (elim_num_big && c->args[j].npi == 0 && res->k == V_LAM && !res->clo.fn) { meta_blocked = 1; return NULL; }
        Native *ih = xalloc(sizeof *ih); ih->code = N_IH; ih->i1 = c->args[j].rec; ih->i2 = target->n; ih->i3 = j; ih->l = elim_lvl;
        for (int i = 0; i < np + nb + K; i++) vl_push(&ih->cap, args->a[i].v, 0);
        for (int i = 0; i < np; i++) vl_push(&ih->cap, target->args.a[i].v, 0);
        for (int i = 0; i < j; i++) vl_push(&ih->cap, target->args.a[np + i].v, 0);
        vl_push(&ih->cap, target->args.a[np + j].v, 0);
        Val *ihv;
        if (c->args[j].npi == 0) {
            Env *e = NULL; for (int i = 0; i < np + j; i++) e = env_push(e, ih->cap.a[np + nb + K + i].v);
            VList a2 = {0};
            for (int i = 0; i < np + nb + K; i++) vl_push(&a2, args->a[i].v, prefix_irr(data, i));
            for (int i = 0; i < c->args[j].nidx; i++) vl_push(&a2, eval(e, c->args[j].idx[i]), 1);
            vl_push(&a2, target->args.a[np + j].v, 0);
            ihv = elim_apply_list(c->args[j].rec, &a2);
        } else { ihv = mkval(V_LAM); ihv->clo.fn = nfn; ihv->clo.data = ih; ihv->name = "y"; }
        res = vapp(res, ihv, 0);
    }
    if (c->nint > 0) {   /* a path constructor: the method is a cube with the prescribed boundary */
        Env *env = NULL;
        for (int i = 0; i < target->args.n; i++) env = env_push(env, target->args.a[i].v);
        if (c->pathmethod) {   /* PathP (i. P (c a i)) (elim .. b0) (elim .. b1) */
            Val *r = target->args.a[np + c->nargs].v;
            Val *ends[2];
            for (int end = 0; end < 2; end++) {
                Env *e0 = NULL;
                for (int i = 0; i < np + c->nargs; i++) e0 = env_push(e0, target->args.a[i].v);
                e0 = env_push(e0, vi(end ? iv_one() : iv_zero()));
                Val *b = eval(e0, c->boundary);
                if (b->k == V_SYS) die("internal: boundary of %s not total at an endpoint", c->name);
                VList a2 = vl_copy(args); a2.n = np + nb + K + D->nidx;   /* the boundary lives at the target's indices */
                vl_push(&a2, b, 0);
                ends[end] = elim_apply_list(data, &a2);
            }
            return vpapp(res, r, ends[0], ends[1]);
        }
        /* (is : I) -> Sub (P (c a is)) phi [faces -> elim .. boundary] */
        for (int q = 0; q < c->nint; q++) res = vapp(res, target->args.a[np + c->nargs + q].v, 0);
        if (!c->boundary) return res;
        Val *bsys = eval(env, c->boundary);
        VList base = vl_copy(args); base.n = np + nb + K + D->nidx;
        Val *img = vsys_map(bsys, elim_of_branch, &base);
        IVal phi = iv_zero();
        if (bsys->k == V_SYS) { for (int i = 0; i < bsys->nbr; i++) phi = iv_or(phi, bsys->br[i].phi->iv); } else phi = iv_one();
        Val **iv = xalloc((D->nidx + 1) * sizeof(Val *));
        for (int j = 0; j < D->nidx; j++) iv[j] = args->a[np + nb + K + j].v;
        Val *P = motive_applied(data, args, iv);
        return vouts(vapp(P, target, 0), vi(phi), img, res);
    }
    return res;
}
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
static Val *elim_apply_list(int data, VList *args) {
    Val *e = mkval(V_NEU); e->h = H_ELIM; e->n = data; e->lvl = elim_lvl;
    Val *r = e;
    for (int i = 0; i < args->n; i++) r = vapp(r, args->a[i].v, args->a[i].irr);
    return r;
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
    if (s->k == V_INS) return s->a;
    Val *v = mkval(V_NEU); v->h = H_OUTS; v->a = A; v->b = phi; v->c = u; v->dom = s; return v;
}

/* ---- application ---- */
/* a rigid definition application to its value: the definition applied to its spine */
Val *unfold_def(Val *v) {
    /* The unfolding is a pure function of the value (definition id, level, spine), so it is computed once and kept in
       the value itself: a rigidity-preserving application is the shared cell, and every later force of the same spine
       hits it. This is the memoization pass - without it each re-application of a nested definition's spine redoes the
       whole body (cost compounding with nesting depth; Finding_Eezott_EvalNoSharing_2026_09_14). Guarded by the spine
       length (neu_app lengthens spines) and the metas version (a solved meta can unstick what the memo took as neutral). */
    if (v->unf && v->unf_n == v->args.n && (v->unf_mv == metas_version || v->unf_stable)) return v->unf;
    int save = meta_blocked; meta_blocked = 0;
    Val *f = def_at(v->n, v->lvl);
    for (int i = 0; i < v->args.n; i++) f = vapply_arg(f, &v->args.a[i]);
    v->unf = f; v->unf_n = v->args.n; v->unf_mv = metas_version; v->unf_stable = !meta_blocked;
    meta_blocked |= save;
    return f;
}

Val *vapp(Val *f, Val *a, int irr) {
    Arg ar = {0}; ar.v = a; ar.irr = irr;
    f = fmeta(f);   /* a definition application stays rigid here; force() unfolds it where a canonical form is needed */
    switch (f->k) {
    case V_LAM: return inst(&f->clo, a);
    case V_NEU:
        if (f->h == H_ELIM) {
            Val *v = neu_app(f, ar);
            Data *D = &datas[f->n];
            int arity = D->nparams + D->nblock + block_ncons(f->n) + D->nidx + 1;
            if (v->args.n == arity) { elim_lvl = f->lvl; Val *r = elim_reduce(f->n, &v->args); if (r) return r; r = elim_hcomp(f->n, &v->args); if (r) return r; }
            return v;
        }
        return neu_app(f, ar);
    case V_DATA: return neu_app(f, ar);
    case V_CON: {
        Val *av = force(a);
        if (av->k == V_NUM && f->args.n == 0 && cons[f->n].data == av->n) {   /* suc of a literal is the literal above */
            int zi, si;
            if (peano_shape(av->n, &zi, &si) && f->n == si) return vnum(av->n, av->lvl, bn_succ(av->num));
        }
        Val *v = neu_app(f, ar);
        Con *C = con_at(f->n, f->lvl); int np = datas[C->data].nparams;
        if (C->nint > 0 && v->args.n == np + C->nargs + C->nint) {   /* a path constructor on a face of its boundary is the boundary */
            Env *env = NULL;
            for (int i = 0; i < v->args.n; i++) env = env_push(env, v->args.a[i].v);
            Val *b = C->boundary ? eval(env, C->boundary) : NULL;
            if (b && b->k != V_SYS) return b;
        }
        return v;
    }
    case V_SYS: { /* a partial function applied pointwise */
        VBranch *br = xalloc((f->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < f->nbr; i++) { br[i].phi = f->br[i].phi; br[i].v = vapp(f->br[i].v, a, irr); }
        return vsys(br, f->nbr);
    }
    default: die("internal: application of a non-function value (kind %d)", f->k);
    }
    return NULL;
}
Val *vpapp(Val *p, Val *r, Val *x, Val *y) {
    if (r->k != V_I) die("internal: path applied to a non-interval");
    p = force(p);
    if (iv_is_zero(r->iv)) return x;
    if (iv_is_one(r->iv)) return y;
    if (p->k == V_LAM) return inst(&p->clo, r);
    if (p->k == V_SYS) {
        VBranch *br = xalloc((p->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < p->nbr; i++) { br[i].phi = p->br[i].phi; br[i].v = vpapp(p->br[i].v, r, x, y); }
        return vsys(br, p->nbr);
    }
    Arg ar = {0}; ar.v = r; ar.papp = 1; ar.x = x; ar.y = y;
    meta_blocked = 1;
    if (p->k == V_NEU || p->k == V_DATA || p->k == V_CON) return neu_app(p, ar);
    die("internal: path application to a non-path value");
    return NULL;
}
Val *pair_snd(Val *p) {
    if (!p->b) p->b = p->clo.fn ? p->clo.fn(p->clo.data, NULL) : eval(p->clo.env, p->clo.t);
    return p->b;
}
Val *vproj(Val *p, int which) {
    p = force(p);
    if (p->k == V_PAIR) return which == 1 ? p->a : pair_snd(p);
    if (p->k == V_SYS) {
        VBranch *br = xalloc((p->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < p->nbr; i++) { br[i].phi = p->br[i].phi; br[i].v = vproj(p->br[i].v, which); }
        return vsys(br, p->nbr);
    }
    Arg ar = {0}; ar.proj = which;
    meta_blocked = 1;
    if (p->k == V_NEU) return neu_app(p, ar);
    die("internal: projection from a non-pair value");
    return NULL;
}
static Val *apply_arg(Val *f, Arg *a) { return a->proj ? vproj(f, a->proj) : a->papp ? vpapp(f, a->v, a->x, a->y) : vapp(f, a->v, a->irr); }
Val *vapply_arg(Val *f, Arg *a) { return apply_arg(f, a); }

/* ---- evaluation ---- */
static Env *subst_env(Env *e, int lv, IVal s);
static IVal face_iv(const Face *f);
Val *eval(Env *env, Term *t) {
    switch (t->k) {
    case T_VAR: return env_get(env, t->n);
    case T_U: { LVal l = t->a ? eval_level(env, t->a) : lv_const(t->n); return t->pre ? vupre_l(l) : vu_l(l); }
    case T_LEVEL: return vlevel();
    case T_LZERO: case T_LSUC: case T_LMAX: case T_LMETA: return vl(eval_level(env, t));
    case T_PI: { Val *v = mkval(V_PI); v->name = t->name; v->irr = t->irr; v->isi = t->isi; v->imp = t->imp; v->dom = eval(env, t->a); v->clo.env = env; v->clo.t = t->b; return v; }
    case T_LAM: { Val *v = mkval(V_LAM); v->name = t->name; v->irr = t->irr; v->isi = t->isi; v->imp = t->imp; v->clo.env = env; v->clo.t = t->a; return v; }
    case T_APP: return vapp(eval(env, t->a), eval(env, t->b), t->irr);
    case T_LET: return eval(env_push(env, eval(env, t->b)), t->c);
    case T_DEF: {   /* rigid: a definition application (H_DEF), unfolded where a canonical form is needed */
        Val *v = mkval(V_NEU); v->h = H_DEF; v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); return v;
    }
    case T_DATA: { Val *v = mkval(V_DATA); v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); return v; }
    case T_CON: { Val *v = mkval(V_CON); v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); return v; }
    case T_NUM: return vnum(t->n, t->a ? eval_level(env, t->a) : lv_const(0), t->num);
    case T_ELIM: { Val *v = mkval(V_NEU); v->h = H_ELIM; v->n = t->n; v->lvl = t->a ? eval_level(env, t->a) : lv_const(0); return v; }
    case T_LVAL: return vl(t->lvl);
    case T_META: { Meta *m = &tmetas[t->n]; if (m->sol) return m->sol; Val *v = mkval(V_NEU); v->h = H_META; v->n = t->n; return v; }
    case T_INTERVAL: return vinterval();
    case T_I0: return vi(iv_zero());
    case T_I1: return vi(iv_one());
    case T_IAND: return vi(iv_and(eval(env, t->a)->iv, eval(env, t->b)->iv));
    case T_IOR: return vi(iv_or(eval(env, t->a)->iv, eval(env, t->b)->iv));
    case T_INEG: return vi(iv_neg(eval(env, t->a)->iv));
    case T_PATHP: { Val *v = mkval(V_PATHP); v->a = eval(env, t->a); v->b = eval(env, t->b); v->c = eval(env, t->c); return v; }
    case T_PAPP: return vpapp(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    case T_PARTIAL: { Val *v = mkval(V_PARTIAL); v->a = eval(env, t->a); v->b = eval(env, t->b); return v; }
    case T_SYS: {   /* each branch is evaluated under the restriction to its face (per conjunct): a branch is only meaningful there */
        int cap = 4, n = 0; VBranch *br = xalloc(cap * sizeof(VBranch));
        for (int i = 0; i < t->nbr; i++) {
            Val *phi = eval(env, t->br[i].face);
            Face *fs; int nf = iv_faces(phi->iv, &fs);
            for (int j = 0; j < nf; j++) {
                if (n == cap) { cap *= 2; VBranch *b2 = xalloc(cap * sizeof(VBranch)); memcpy(b2, br, n * sizeof(VBranch)); br = b2; }
                Env *env_f = env;
                for (int k = 0; k < fs[j].n; k++) env_f = subst_env(env_f, fs[j].var[k], fs[j].val[k] ? iv_one() : iv_zero());
                br[n].phi = vi(face_iv(&fs[j])); br[n].v = eval(env_f, t->br[i].body); n++;
            }
        }
        return vsys(br, n);
    }
    case T_TRANSP: return vtransp(eval(env, t->a), eval(env, t->b), eval(env, t->c));
    case T_HCOMP: return vhcomp(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    case T_SUB: { Val *v = mkval(V_SUB); v->a = eval(env, t->a); v->b = eval(env, t->b); v->c = eval(env, t->c); return v; }
    case T_SIGMA: { Val *v = mkval(V_SIGMA); v->name = t->name; v->irr = t->irr; v->dom = eval(env, t->a); v->clo.env = env; v->clo.t = t->b; return v; }
    case T_PAIR: {
        Val *v = mkval(V_PAIR); v->irr = t->irr; v->n = t->n; v->a = eval(env, t->a);
        if (t->irr) { v->b = NULL; v->clo.env = env; v->clo.t = t->b; }   /* lazy: forced by snd only */
        else v->b = eval(env, t->b);
        return v;
    }
    case T_IRR: return mkval(V_IRR);
    case T_FST: return vproj(eval(env, t->a), 1);
    case T_SND: return vproj(eval(env, t->a), 2);
    case T_GLUE: { Val *g = vglue(eval(env, t->a), eval(env, t->b), eval(env, t->c)); if (g->k == V_GLUE) g->lvl = t->d ? eval_level(env, t->d) : lv_const(t->n); return g; }
    case T_GLUEEL: return vglueel(eval(env, t->a), eval(env, t->b), eval(env, t->c));
    case T_UNGLUE: return vunglue(eval(env, t->b), eval(env, t->c), eval(env, t->d), eval(env, t->a));
    case T_INS: { Val *v = mkval(V_INS); v->a = eval(env, t->a); return v; }
    case T_OUTS: return vouts(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    }
    return NULL;
}

/* ---- restriction to a face ---- */
static Env *subst_env(Env *e, int lv, IVal s) {
    if (!e) return NULL;
    Env *n = xalloc(sizeof *n); n->v = subst_val(e->v, lv, s); n->next = subst_env(e->next, lv, s); return n;
}
/* closures built by the Kan rules with plain structs of values: the struct is a Val* array of known length */
static void *caps_subst(void *data, int n, int lv, IVal s) {
    Caps *c = data, *r = xalloc(sizeof *r); *r = *c;
    for (int i = 0; i < n; i++) r->v[i] = subst_val(c->v[i], lv, s);
    return r;
}
static void subst_clo(Clo *dst, const Clo *src, int lv, IVal s) {
    *dst = *src;
    dst->iarg = NULL; dst->ires = NULL; dst->imv = 0;   /* the substitution changes what the closure computes */
    if (src->fn) {
        if (src->fn == natfn) {
            NatNative *nn = src->data, *m = xalloc(sizeof *m); *m = *nn;
            m->fallback = subst_val(nn->fallback, lv, s); if (nn->arg1) m->arg1 = subst_val(nn->arg1, lv, s);
            dst->data = m; return;
        }
        if (src->fn != nfn) { dst->data = caps_subst(src->data, ((Caps *)src->data)->n, lv, s); return; }
        Native *nt = src->data, *nn = xalloc(sizeof *nn); *nn = *nt; nn->cap = (VList){0};
        for (int i = 0; i < nt->cap.n; i++) vl_push(&nn->cap, subst_val(nt->cap.a[i].v, lv, s), nt->cap.a[i].irr);
        dst->data = nn;
    } else dst->env = subst_env(src->env, lv, s);
}
Val *restrict_val(Val *v, const Face *f) {
    if (!f) return v;
    for (int i = 0; i < f->n; i++) v = subst_val(v, f->var[i], f->val[i] ? iv_one() : iv_zero());
    return v;
}
Val *subst_val(Val *v, int lv, IVal s) {
    switch (v->k) {
    case V_U: case V_INTERVAL: case V_L: case V_LEVEL: return v;
    case V_I: return vi(iv_subst(v->iv, lv, s));
    case V_LAM: { Val *r = mkval(V_LAM); *r = *v; subst_clo(&r->clo, &v->clo, lv, s); return r; }
    case V_PI: { Val *r = mkval(V_PI); *r = *v; r->dom = subst_val(v->dom, lv, s); subst_clo(&r->clo, &v->clo, lv, s); return r; }
    case V_PATHP: { Val *r = mkval(V_PATHP); r->a = subst_val(v->a, lv, s); r->b = subst_val(v->b, lv, s); r->c = subst_val(v->c, lv, s); return r; }
    case V_PARTIAL: { Val *r = mkval(V_PARTIAL); r->a = subst_val(v->a, lv, s); r->b = subst_val(v->b, lv, s); return r; }
    case V_SUB: { Val *r = mkval(V_SUB); r->a = subst_val(v->a, lv, s); r->b = subst_val(v->b, lv, s); r->c = subst_val(v->c, lv, s); return r; }
    case V_INS: { Val *r = mkval(V_INS); r->a = subst_val(v->a, lv, s); return r; }
    case V_SIGMA: { Val *r = mkval(V_SIGMA); *r = *v; r->dom = subst_val(v->dom, lv, s); subst_clo(&r->clo, &v->clo, lv, s); return r; }
    case V_PAIR: {
        Val *r = mkval(V_PAIR); r->irr = v->irr; r->n = v->n; r->a = subst_val(v->a, lv, s);
        if (v->b) r->b = subst_val(v->b, lv, s); else { r->b = NULL; subst_clo(&r->clo, &v->clo, lv, s); }
        return r;
    }
    case V_IRR: return v;
    case V_SYS: {
        VBranch *br = xalloc((v->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < v->nbr; i++) { br[i].phi = subst_val(v->br[i].phi, lv, s); br[i].v = subst_val(v->br[i].v, lv, s); }
        return vsys(br, v->nbr);
    }
    case V_NUM: return v;   /* closed */
    case V_DATA: case V_CON: {
        Val *r = mkval(v->k); r->n = v->n; r->lvl = v->lvl; r->args = (VList){0};
        for (int i = 0; i < v->args.n; i++) { Arg a = v->args.a[i]; if (a.v) a.v = subst_val(a.v, lv, s); if (a.papp) { a.x = subst_val(a.x, lv, s); a.y = subst_val(a.y, lv, s); } a.irr = 0; if (v->k == V_CON) r = vapp(r, a.v, 0); else vl_push_arg(&r->args, a); }
        return r;
    }
    case V_GLUE: { Val *g = vglue(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s)); if (g->k == V_GLUE) g->lvl = v->lvl; return g; }
    case V_GLUEEL: return vglueel(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s));
    case V_NEU: {
        Val *head;
        switch (v->h) {
        case H_VAR: head = vvar(v->n); break;
        case H_ELIM: head = mkval(V_NEU); head->h = H_ELIM; head->n = v->n; head->lvl = v->lvl; break;
        case H_TRANSP: head = vtransp(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s)); break;
        case H_HCOMP: head = vhcomp(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s), subst_val(v->dom, lv, s)); break;
        case H_OUTS: head = vouts(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s), subst_val(v->dom, lv, s)); break;
        case H_UNGLUE: head = vunglue(subst_val(v->a, lv, s), subst_val(v->b, lv, s), subst_val(v->c, lv, s), subst_val(v->dom, lv, s)); break;
        case H_META: { Val *fv = force(v); if (fv != v) return subst_val(fv, lv, s); head = mkval(V_NEU); head->h = H_META; head->n = v->n; break; }
        case H_DEF: head = mkval(V_NEU); head->h = H_DEF; head->n = v->n; head->lvl = v->lvl; break;
        default: die("internal: unknown neutral head");
        }
        for (int i = 0; i < v->args.n; i++) { Arg a = v->args.a[i]; if (a.v) a.v = subst_val(a.v, lv, s); if (a.papp) { a.x = subst_val(a.x, lv, s); a.y = subst_val(a.y, lv, s); } head = apply_arg(head, &a); }
        return head;
    }
    }
    return v;
}

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
    Val *tfs = vnative(N_GLUE_HF, 0, 0, 0, 4, Te, psi, u, u0);
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
   a proof nobody reads. */
Val *nf_force(Val *v) {
    v = force(v);
    if (v->k != V_PAIR) return v;
    Val *w = mkval(V_PAIR); w->irr = v->irr; w->n = v->n; w->a = nf_force(v->a);
    if (!v->irr) w->b = nf_force(pair_snd(v));
    return w;
}
Term *quote(int depth, Val *v) {
    v = fmeta(v);   /* metas only: a rigid definition application quotes as the application (printing forces first) */
    switch (v->k) {
    case V_U: { int n; if (lv_is_const(v->lvl, &n)) return v->pre ? mk_upre(n) : mk_u(n); Term *t = mk_u(0); t->pre = v->pre; t->a = quote_level(depth, v->lvl); return t; }
    case V_L: return quote_level(depth, v->lvl);
    case V_LEVEL: return mk_term(T_LEVEL, NULL, NULL, NULL, NULL);
    case V_INTERVAL: return mk(T_INTERVAL);
    case V_I: return quote_iv(depth, v->iv);
    case V_LAM: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        Term *t = mk_lam(v->name ? v->name : "x", quote(depth + 1, inst(&v->clo, x)), v->irr); t->isi = v->isi; t->imp = v->imp; return t;
    }
    case V_PI: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        Term *t = mk_pi(v->name ? v->name : "_", quote(depth, v->dom), quote(depth + 1, inst(&v->clo, x)), v->irr); t->isi = v->isi; t->imp = v->imp; return t;
    }
    case V_PATHP: return mk_term(T_PATHP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
    case V_PARTIAL: return mk_term(T_PARTIAL, quote(depth, v->a), quote(depth, v->b), NULL, NULL);
    case V_SUB: return mk_term(T_SUB, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
    case V_INS: return mk_term(T_INS, quote(depth, v->a), NULL, NULL, NULL);
    case V_SIGMA: { Term *t = mk_term(T_SIGMA, quote(depth, v->dom), quote(depth + 1, inst(&v->clo, vvar(depth))), NULL, NULL); t->name = v->name ? v->name : "_"; t->irr = v->irr; return t; }
    case V_PAIR: {   /* an irrelevant component is elided from the normal form */
        Term *t = mk_term(T_PAIR, quote(depth, v->a), v->irr ? mk_term(T_IRR, NULL, NULL, NULL, NULL) : quote(depth, v->b), NULL, NULL);
        t->irr = v->irr; t->n = v->n; return t;
    }
    case V_IRR: return mk_term(T_IRR, NULL, NULL, NULL, NULL);
    case V_GLUE: { Term *t = mk_term(T_GLUE, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL); if (!lv_is_const(v->lvl, &t->n)) t->d = quote_level(depth, v->lvl); return t; }
    case V_GLUEEL: return mk_term(T_GLUEEL, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
    case V_SYS: {
        Term *t = mk(T_SYS); t->nbr = v->nbr; t->br = xalloc((v->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < v->nbr; i++) { t->br[i].face = quote(depth, v->br[i].phi); t->br[i].body = quote(depth, v->br[i].v); }
        return t;
    }
    case V_NUM: return mk_num(v->n, quote_level(depth, v->lvl), v->num);
    case V_NEU: case V_DATA: case V_CON: {
        Term *h;
        if (v->k == V_DATA) h = mk_ref_l(T_DATA, v->n, quote_level(depth, v->lvl));
        else if (v->k == V_CON) h = mk_ref_l(T_CON, v->n, quote_level(depth, v->lvl));
        else if (v->h == H_ELIM) h = mk_ref_l(T_ELIM, v->n, quote_level(depth, v->lvl));
        else if (v->h == H_TRANSP) h = mk_term(T_TRANSP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
        else if (v->h == H_HCOMP) h = mk_term(T_HCOMP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), quote(depth, v->dom));
        else if (v->h == H_OUTS) h = mk_term(T_OUTS, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), quote(depth, v->dom));
        else if (v->h == H_UNGLUE) h = mk_term(T_UNGLUE, quote(depth, v->dom), quote(depth, v->a), quote(depth, v->b), quote(depth, v->c));
        else if (v->h == H_META) { h = mk_term(T_META, NULL, NULL, NULL, NULL); h->n = v->n; }
        else if (v->h == H_DEF) h = mk_ref_l(T_DEF, v->n, quote_level(depth, v->lvl));
        else h = mk_var(depth - 1 - v->n);
        for (int i = 0; i < v->args.n; i++) {
            Arg *a = &v->args.a[i];
            if (a->proj) h = mk_term(a->proj == 1 ? T_FST : T_SND, h, NULL, NULL, NULL);
            else if (a->papp) h = mk_term(T_PAPP, h, quote(depth, a->v), quote(depth, a->x), quote(depth, a->y));
            else h = mk_app(h, quote(depth, a->v), a->irr);
        }
        return h;
    }
    }
    return NULL;
}
int val_mentions_ivar(int depth, Val *v, int level) { return term_mentions_var(quote(depth, v), depth - 1 - level); }

/* ---- conversion ---- */
static int conv_spine(int depth, VList *a, VList *b) {
    if (a->n != b->n) return 0;
    for (int i = 0; i < a->n; i++) {
        if (a->a[i].proj != b->a[i].proj) return 0;   /* path and plain application to an interval coincide */
        if (a->a[i].proj) continue;
        if ((a->a[i].irr & 2) && (b->a[i].irr & 2)) continue;   /* the argument of an irrelevant binder */
        if (!conv(depth, a->a[i].v, b->a[i].v)) return 0;
    }
    return 1;
}
static int conv_sys(int depth, Val *a, Val *b) {   /* partial elements agree on every face of their (common) support */
    Val *s = a->k == V_SYS ? a : b;
    IVal phi = iv_zero();
    for (int i = 0; i < s->nbr; i++) phi = iv_or(phi, s->br[i].phi->iv);
    Face *fs; int nf = iv_faces(phi, &fs);
    for (int i = 0; i < nf; i++) {
        Val *x = vsys_at(a, &fs[i]), *y = vsys_at(b, &fs[i]);
        if (!x || !y || !conv(depth, x, y)) return 0;
    }
    return 1;
}
static int conv1(int depth, Val *a, Val *b);
/* the levels of two occurrences of a global agree (only polymorphic globals take one) */
static int lvl_conv(TKind k, int id, LVal a, LVal b) { return !ref_poly(k, id) || lv_enforce_eq(a, b) == 1; }
/* conversion is transactional: level constraints added by a comparison that fails are rolled back */
int conv(int depth, Val *a, Val *b) {
    LMark m = lstore_mark(); MMark mm = meta_mark();
    int r = conv1(depth, a, b);
    if (!r) { lstore_rollback(m); meta_rollback(mm); }
    return r;
}
static int conv1_b(int depth, Val *a, Val *b);
static int conv_fail_logged;
int conv_depth_now;
static int conv1(int depth, Val *a, Val *b) {
    conv_depth_now++;
    int r = conv1_b(depth, a, b);
    conv_depth_now--;
    if (!r && conv_fail_logged < 20 && getenv("EEZOTT_CONV_TRACE")) {
        conv_fail_logged++;
        fprintf(stderr, "[conv] #%d depth %d call-depth %d: ", conv_fail_logged, depth, conv_depth_now);
        const char *nm[2048] = {0};
        term_print(stderr, quote(0, a), nm, 0); fputs("   !=   ", stderr);
        term_print(stderr, quote(0, b), nm, 0); fputc('\n', stderr);
        if ((a->k == V_I || b->k == V_I) && getenv("EEZOTT_CONV_TRAP")) __builtin_trap();
    }
    return r;
}
static int conv1_b(int depth, Val *a, Val *b) {
    a = fmeta(a); b = fmeta(b);
    /* definition applications stay rigid: the same definition compares by spine congruence, and the spine's arguments
       at .() binders (irr bit 2) are skipped - proofs differing only there are equal by construction (compareIrrelevant
       in Agda; the H_DEF plan). Different definitions (or a rigid against something else): unfold and continue. */
    for (;;) {
        int ad = a->k == V_NEU && a->h == H_DEF, bd = b->k == V_NEU && b->h == H_DEF;
        if (ad && bd) {
            /* the fast path: the same definition, spines convertible (the .() arguments skipped) - equal by congruence.
               Otherwise fall back to unfolding both, as if the spine comparison had never happened. */
            if (a->n == b->n && a->args.n == b->args.n && lvl_conv(T_DEF, a->n, a->lvl, b->lvl)
                && conv_spine(depth, &a->args, &b->args)) return 1;
            a = fmeta(unfold_def(a)); b = fmeta(unfold_def(b)); continue;
        }
        if (ad) { a = fmeta(unfold_def(a)); continue; }
        if (bd) { b = fmeta(unfold_def(b)); continue; }
        break;
    }
    /* a level variable is a level value in the context and a neutral variable under a binder opened by conversion */
    if (a->k == V_L && b->k == V_NEU && b->h == H_VAR && b->args.n == 0) return lv_enforce_eq(a->lvl, lv_var(b->n)) == 1;
    if (b->k == V_L && a->k == V_NEU && a->h == H_VAR && a->args.n == 0) return lv_enforce_eq(b->lvl, lv_var(a->n)) == 1;
    if (a == b) return 1;
    {   /* a meta: solved by pattern unification, or the constraint is postponed */
        int am = a->k == V_NEU && a->h == H_META, bm = b->k == V_NEU && b->h == H_META;
        if (am && bm && a->n == b->n) {
            LMark m = lstore_mark(); MMark mm = meta_mark();
            if (conv_spine(depth, &a->args, &b->args)) return 1;
            lstore_rollback(m); meta_rollback(mm); meta_postpone(depth, a, b); return 1;
        }
        if (am) return unify_meta(depth, a, b);
        if (bm) return unify_meta(depth, b, a);
    }
    /* literals (M15): equal numbers; against constructors, one constructor at a time */
    if (a->k == V_NUM && b->k == V_NUM) return a->n == b->n && lvl_conv(T_DATA, a->n, a->lvl, b->lvl) && bn_cmp(a->num, b->num) == 0;
    if (a->k == V_NUM && b->k == V_CON) a = num_view(a);
    if (b->k == V_NUM && a->k == V_CON) b = num_view(b);
    if (a->k == V_SYS || b->k == V_SYS) return conv_sys(depth, a, b);
    if (a->k == V_LAM || b->k == V_LAM) {          /* eta */
        int isi = (a->k == V_LAM ? a->isi : b->isi);
        Val *x = isi ? vivar(depth) : vvar(depth);
        /* a neutral applied to an interval is the same application whether it was formed as a path or as a function of I */
        Val *fa = a->k == V_LAM ? inst(&a->clo, x) : vapp(a, x, 0);
        Val *fb = b->k == V_LAM ? inst(&b->clo, x) : vapp(b, x, 0);
        return conv(depth + 1, fa, fb);
    }
    if (a->k == V_IRR || b->k == V_IRR) die("internal: an elided irrelevant value reached conversion");
    if (a->k == V_PAIR || b->k == V_PAIR) {   /* eta; an irrelevant second component is not compared */
        int irr = (a->k == V_PAIR && a->irr) || (b->k == V_PAIR && b->irr);
        return conv(depth, vproj(a, 1), vproj(b, 1)) && (irr || conv(depth, vproj(a, 2), vproj(b, 2)));
    }
    if (a->k != b->k) return 0;
    switch (a->k) {
    case V_U: return a->pre == b->pre && lv_enforce_eq(a->lvl, b->lvl) == 1;
    case V_L: return lv_enforce_eq(a->lvl, b->lvl) == 1;
    case V_LEVEL: return 1;
    case V_SIGMA: {
        if (a->irr != b->irr || !conv(depth, a->dom, b->dom)) return 0;
        Val *x = vvar(depth);
        return conv(depth + 1, inst(&a->clo, x), inst(&b->clo, x));
    }
    case V_INTERVAL: return 1;
    case V_I: return iv_eq(a->iv, b->iv);
    case V_PI: {
        if (!conv(depth, a->dom, b->dom)) return 0;
        Val *x = a->isi ? vivar(depth) : vvar(depth);
        return conv(depth + 1, inst(&a->clo, x), inst(&b->clo, x));
    }
    case V_PATHP: return conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c);
    case V_PARTIAL: return conv(depth, a->a, b->a) && conv(depth, a->b, b->b);
    case V_SUB: return conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c);
    case V_INS: return conv(depth, a->a, b->a);
    case V_GLUE: return conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c);
    case V_GLUEEL: return conv(depth, a->b, b->b) && conv(depth, a->a, b->a);
    case V_NEU:
        if (a->h != b->h) return 0;
        if (a->h == H_TRANSP) { if (!(conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c))) return 0; }
        else if (a->h == H_HCOMP) { if (!(conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c) && conv(depth, a->dom, b->dom))) return 0; }
        else if (a->h == H_OUTS || a->h == H_UNGLUE) { if (!conv(depth, a->dom, b->dom)) return 0; }
        else if (a->n != b->n || (a->h != H_VAR && !lvl_conv(T_ELIM, a->n, a->lvl, b->lvl))) return 0;   /* a variable's n is its level, not a global id */
        return conv_spine(depth, &a->args, &b->args);
    case V_DATA: case V_CON: return a->n == b->n && lvl_conv(a->k == V_DATA ? T_DATA : T_CON, a->n, a->lvl, b->lvl) && conv_spine(depth, &a->args, &b->args);
    default: return 0;
    }
}
