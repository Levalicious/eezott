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

/* ---- memory / errors ---- */
void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) die("out of memory"); return p; }
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
Term *mk_pi(const char *x, Term *a, Term *b, int irr) { Term *t = mk(T_PI); t->name = x; t->a = a; t->b = b; t->irr = irr; t->isi = (a->k == T_INTERVAL); return t; }
Term *mk_lam(const char *x, Term *body, int irr) { Term *t = mk(T_LAM); t->name = x; t->a = body; t->irr = irr; return t; }
Term *mk_app(Term *f, Term *a, int irr) { Term *t = mk(T_APP); t->a = f; t->b = a; t->irr = irr; return t; }
Term *mk_let(const char *x, Term *ty, Term *v, Term *body, int irr) { Term *t = mk(T_LET); t->name = x; t->a = ty; t->b = v; t->c = body; t->irr = irr; return t; }
Term *mk_ref(TKind k, int id) { Term *t = mk(k); t->n = id; return t; }
Term *mk_term(TKind k, Term *a, Term *b, Term *c, Term *d) { Term *t = mk(k); t->a = a; t->b = b; t->c = c; t->d = d; return t; }

Term *shift2(Term *t, int cut1, int by1, int cut2, int by2) {
    if (!t) return NULL;
    Term *r;
    switch (t->k) {
    case T_VAR:
        if (t->n >= cut2) return mk_var(t->n + by2);
        if (t->n >= cut1) return mk_var(t->n + by1);
        return t;
    case T_U: case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_INTERVAL: case T_I0: case T_I1: return t;
    case T_PI:  r = mk_pi(t->name, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1 + 1, by1, cut2 + 1, by2), t->irr); r->isi = t->isi; return r;
    case T_LAM: r = mk_lam(t->name, shift2(t->a, cut1 + 1, by1, cut2 + 1, by2), t->irr); r->isi = t->isi; return r;
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
        r->n = t->n; r->irr = t->irr; r->name = t->name; return r;
    }
}
Term *shift(Term *t, int cut, int by) { return shift2(t, cut, by, cut, by); }

int term_eq(Term *a, Term *b) {
    if (a == b) return 1;
    if (!a || !b || a->k != b->k) return 0;
    switch (a->k) {
    case T_VAR: case T_U: case T_DEF: case T_DATA: case T_CON: case T_ELIM: return a->n == b->n;
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
    case T_U: case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_INTERVAL: case T_I0: case T_I1: return 0;
    case T_PI: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx + 1);
    case T_LAM: return term_mentions_var(t->a, idx + 1);
    case T_LET: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx) || term_mentions_var(t->c, idx + 1);
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (term_mentions_var(t->br[i].face, idx) || term_mentions_var(t->br[i].body, idx)) return 1; return 0;
    default: return term_mentions_var(t->a, idx) || term_mentions_var(t->b, idx) || term_mentions_var(t->c, idx) || term_mentions_var(t->d, idx);
    }
}

/* printing with names: names[] indexed by de Bruijn level, depth = number bound */
static void tp(FILE *f, Term *t, const char **names, int depth, int prec) {
    switch (t->k) {
    case T_VAR: {
        int lvl = depth - 1 - t->n;
        if (lvl >= 0 && lvl < depth && names[lvl]) fprintf(f, "%s", names[lvl]); else fprintf(f, "#%d", t->n);
        break; }
    case T_U: if (t->n) fprintf(f, "U %d", t->n); else fprintf(f, "U"); break;
    case T_DEF: fprintf(f, "%s", defs[t->n].name); break;
    case T_DATA: fprintf(f, "%s", datas[t->n].name); break;
    case T_CON: fprintf(f, "%s", cons[t->n].name); break;
    case T_ELIM: fprintf(f, "elim %s", datas[t->n].name); break;
    case T_INTERVAL: fputs("I", f); break;
    case T_I0: fputs("i0", f); break;
    case T_I1: fputs("i1", f); break;
    case T_INEG: fputs("~ ", f); tp(f, t->a, names, depth, 3); break;
    case T_IAND: if (prec > 0) fputc('(', f); tp(f, t->a, names, depth, 1); fputs(" /\\ ", f); tp(f, t->b, names, depth, 1); if (prec > 0) fputc(')', f); break;
    case T_IOR:  if (prec > 0) fputc('(', f); tp(f, t->a, names, depth, 1); fputs(" \\/ ", f); tp(f, t->b, names, depth, 1); if (prec > 0) fputc(')', f); break;
    case T_PI: {
        if (prec > 0) fputc('(', f);
        const char *nm = t->name && strcmp(t->name, "_") ? t->name : NULL;
        if (nm) { fprintf(f, "(%s : ", nm); tp(f, t->a, names, depth, 0); fprintf(f, ") -> "); }
        else { tp(f, t->a, names, depth, 1); fprintf(f, " -> "); }
        names[depth] = nm ? nm : "_"; tp(f, t->b, names, depth + 1, 0);
        if (prec > 0) fputc(')', f);
        break; }
    case T_LAM: {
        if (prec > 0) fputc('(', f);
        fprintf(f, "\\%s -> ", t->name); names[depth] = t->name; tp(f, t->a, names, depth + 1, 0);
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
Val *vu(int l) { Val *v = mkval(V_U); v->n = l; return v; }
Val *vi(IVal iv) { Val *v = mkval(V_I); v->iv = iv; return v; }
Val *vivar(int level) { return vi(iv_var(level)); }
static Val *vinterval(void) { return mkval(V_INTERVAL); }
static int fresh_level = 1 << 20;      /* scratch interval variables, never in a context */
static Val *fresh_ivar(void) { return vivar(fresh_level++); }

/* native closures: a code and captured values */
enum { N_IH = 1, N_LINE_DOM, N_LINE_COD_V, N_TRANSP_V, N_LINE_IOR, N_LINE_IAND, N_HCOMP_PI_SIDES, N_PATH_HCOMP_SIDES,
       N_LINE_PATH_AT, N_PATH_TRANSP_SIDES, N_FWD_SIDES, N_FILL, N_FILL_SIDES, N_TFILL, N_DATA_ARG_LINE, N_SYS_PROJ,
       N_CONST, N_ELIM_MOTIVE_LINE, N_ELIM_SIDES };
typedef struct { int code; int i1, i2, i3; VList cap; } Native;

static Val *native_apply(Native *nt, Val *arg);
Val *inst(Clo *c, Val *v) {
    if (c->fn) return c->fn(c->data, v);
    return eval(env_push(c->env, v), c->t);
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
    Val *v = mkval(f->k); *v = *f; v->args = vl_copy(&f->args); vl_push_arg(&v->args, a); return v;
}
static Val *elim_apply_list(int data, VList *args);

/* ---- induction hypotheses (native closure N_IH) ----
   cap = base (params, motive, methods), tele (params, previous args), ys, aj; i1=data i2=con i3=j; ys count = cap.n - nb - nt - 1 */
static Val *ih_apply(Native *c, Val *y) {
    int nb = datas[c->i1].nparams + 1 + datas[c->i1].ncons;
    Con *C = &cons[c->i2]; int j = c->i3; int nt = datas[c->i1].nparams + j;
    ConArg *ca = &C->args[j];
    Native *d = xalloc(sizeof *d); *d = *c; d->cap = vl_copy(&c->cap);
    /* insert y before the trailing aj */
    Arg aj = d->cap.a[d->cap.n - 1]; d->cap.n--; vl_push(&d->cap, y, 0); vl_push_arg(&d->cap, aj);
    int ny = d->cap.n - nb - nt - 1;
    if (ny < ca->npi) { Val *v = mkval(V_LAM); v->clo.fn = nfn; v->clo.data = d; v->name = "y"; return v; }
    Env *e = NULL; for (int i = 0; i < nt; i++) e = env_push(e, d->cap.a[nb + i].v);
    for (int i = 0; i < ny; i++) e = env_push(e, d->cap.a[nb + nt + i].v);
    VList args = {0};
    for (int i = 0; i < nb; i++) vl_push(&args, d->cap.a[i].v, i < datas[c->i1].nparams + 1);
    for (int i = 0; i < ca->nidx; i++) vl_push(&args, eval(e, ca->idx[i]), 1);
    Val *t = d->cap.a[d->cap.n - 1].v; for (int i = 0; i < ny; i++) t = vapp(t, d->cap.a[nb + nt + i].v, 0);
    vl_push(&args, t, 0);
    return elim_apply_list(c->i1, &args);
}

/* iota: the eliminator's full spine ends in a constructor */
static Val *elim_reduce(int data, VList *args) {
    Data *D = &datas[data];
    int np = D->nparams, k = D->ncons;
    Val *target = args->a[args->n - 1].v;
    if (target->k != V_CON) return NULL;
    Con *c = &cons[target->n];
    if (c->data != data || target->args.n != np + c->nargs) return NULL;
    Val *res = args->a[np + 1 + c->ci].v;
    for (int j = 0; j < c->nargs; j++) res = vapp(res, target->args.a[np + j].v, c->args[j].irr);
    for (int j = 0; j < c->nargs; j++) {
        if (!c->args[j].isrec) continue;
        Native *ih = xalloc(sizeof *ih); ih->code = N_IH; ih->i1 = data; ih->i2 = target->n; ih->i3 = j;
        for (int i = 0; i < np + 1 + k; i++) vl_push(&ih->cap, args->a[i].v, 0);
        for (int i = 0; i < np; i++) vl_push(&ih->cap, target->args.a[i].v, 0);
        for (int i = 0; i < j; i++) vl_push(&ih->cap, target->args.a[np + i].v, 0);
        vl_push(&ih->cap, target->args.a[np + j].v, 0);
        Val *ihv;
        if (c->args[j].npi == 0) {
            Env *e = NULL; for (int i = 0; i < np + j; i++) e = env_push(e, ih->cap.a[np + 1 + k + i].v);
            VList a2 = {0};
            for (int i = 0; i < np + 1 + k; i++) vl_push(&a2, args->a[i].v, i < np + 1);
            for (int i = 0; i < c->args[j].nidx; i++) vl_push(&a2, eval(e, c->args[j].idx[i]), 1);
            vl_push(&a2, target->args.a[np + j].v, 0);
            ihv = elim_apply_list(data, &a2);
        } else { ihv = mkval(V_LAM); ihv->clo.fn = nfn; ihv->clo.data = ih; ihv->name = "y"; }
        res = vapp(res, ihv, 0);
    }
    return res;
}

/* the eliminator through a formal composition (a normal form on indexed families, and on HITs later):
     elim D p P m idx (hcomp A phi u u0) = comp (\k. P idx (hfill A phi u u0 k)) phi (\k. elim .. (u k)) (elim .. u0)   */
static Val *vcomp(Val *line, Val *phi, Val *u, Val *u0);
static Val *apply_to(Val *b, void *E) { return vapp((Val *)E, b, 0); }
static Val *elim_hcomp(int data, VList *args) {
    Data *D = &datas[data];
    int np = D->nparams, k = D->ncons, m = D->nidx;
    Val *t = args->a[args->n - 1].v;
    if (t->k != V_NEU || t->h != H_HCOMP || t->a->k != V_DATA || t->a->n != data) return NULL;
    Val *E = mkval(V_NEU); E->h = H_ELIM; E->n = data;
    for (int i = 0; i < args->n - 1; i++) E = vapp(E, args->a[i].v, args->a[i].irr);
    Native *nt = xalloc(sizeof *nt); nt->code = N_ELIM_MOTIVE_LINE; nt->i1 = m;
    vl_push(&nt->cap, args->a[np].v, 0);
    for (int j = 0; j < m; j++) vl_push(&nt->cap, args->a[np + 1 + k + j].v, 0);
    vl_push(&nt->cap, vnative(N_FILL, 1, 0, 0, 4, t->a, t->b, t->c, t->dom), 0);
    Val *line = mkval(V_LAM); line->clo.fn = nfn; line->clo.data = nt; line->isi = 1; line->name = "k";
    return vcomp(line, t->b, vnative(N_ELIM_SIDES, 0, 0, 0, 2, E, t->c), vapp(E, t->dom, 0));
}
static Val *elim_apply_list(int data, VList *args) {
    Val *e = mkval(V_NEU); e->h = H_ELIM; e->n = data;
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
Val *vapp(Val *f, Val *a, int irr) {
    Arg ar = {0}; ar.v = a; ar.irr = irr;
    switch (f->k) {
    case V_LAM: return inst(&f->clo, a);
    case V_NEU:
        if (f->h == H_ELIM) {
            Val *v = neu_app(f, ar);
            Data *D = &datas[f->n];
            int arity = D->nparams + 1 + D->ncons + D->nidx + 1;
            if (v->args.n == arity) { Val *r = elim_reduce(f->n, &v->args); if (r) return r; r = elim_hcomp(f->n, &v->args); if (r) return r; }
            return v;
        }
        return neu_app(f, ar);
    case V_DATA: case V_CON: return neu_app(f, ar);
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
    if (iv_is_zero(r->iv)) return x;
    if (iv_is_one(r->iv)) return y;
    if (p->k == V_LAM) return inst(&p->clo, r);
    if (p->k == V_SYS) {
        VBranch *br = xalloc((p->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < p->nbr; i++) { br[i].phi = p->br[i].phi; br[i].v = vpapp(p->br[i].v, r, x, y); }
        return vsys(br, p->nbr);
    }
    Arg ar = {0}; ar.v = r; ar.papp = 1; ar.x = x; ar.y = y;
    if (p->k == V_NEU || p->k == V_DATA || p->k == V_CON) return neu_app(p, ar);
    die("internal: path application to a non-path value");
    return NULL;
}
static Val *apply_arg(Val *f, Arg *a) { return a->papp ? vpapp(f, a->v, a->x, a->y) : vapp(f, a->v, a->irr); }

/* ---- evaluation ---- */
Val *eval(Env *env, Term *t) {
    switch (t->k) {
    case T_VAR: return env_get(env, t->n);
    case T_U: return vu(t->n);
    case T_PI: { Val *v = mkval(V_PI); v->name = t->name; v->irr = t->irr; v->isi = t->isi; v->dom = eval(env, t->a); v->clo.env = env; v->clo.t = t->b; return v; }
    case T_LAM: { Val *v = mkval(V_LAM); v->name = t->name; v->irr = t->irr; v->isi = t->isi; v->clo.env = env; v->clo.t = t->a; return v; }
    case T_APP: return vapp(eval(env, t->a), eval(env, t->b), t->irr);
    case T_LET: return eval(env_push(env, eval(env, t->b)), t->c);
    case T_DEF: return defs[t->n].vval;
    case T_DATA: { Val *v = mkval(V_DATA); v->n = t->n; return v; }
    case T_CON: { Val *v = mkval(V_CON); v->n = t->n; return v; }
    case T_ELIM: { Val *v = mkval(V_NEU); v->h = H_ELIM; v->n = t->n; return v; }
    case T_INTERVAL: return vinterval();
    case T_I0: return vi(iv_zero());
    case T_I1: return vi(iv_one());
    case T_IAND: return vi(iv_and(eval(env, t->a)->iv, eval(env, t->b)->iv));
    case T_IOR: return vi(iv_or(eval(env, t->a)->iv, eval(env, t->b)->iv));
    case T_INEG: return vi(iv_neg(eval(env, t->a)->iv));
    case T_PATHP: { Val *v = mkval(V_PATHP); v->a = eval(env, t->a); v->b = eval(env, t->b); v->c = eval(env, t->c); return v; }
    case T_PAPP: return vpapp(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    case T_PARTIAL: { Val *v = mkval(V_PARTIAL); v->a = eval(env, t->a); v->b = eval(env, t->b); return v; }
    case T_SYS: {
        VBranch *br = xalloc((t->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < t->nbr; i++) { br[i].phi = eval(env, t->br[i].face); br[i].v = eval(env, t->br[i].body); }
        return vsys(br, t->nbr);
    }
    case T_TRANSP: return vtransp(eval(env, t->a), eval(env, t->b), eval(env, t->c));
    case T_HCOMP: return vhcomp(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    case T_SUB: { Val *v = mkval(V_SUB); v->a = eval(env, t->a); v->b = eval(env, t->b); v->c = eval(env, t->c); return v; }
    case T_INS: { Val *v = mkval(V_INS); v->a = eval(env, t->a); return v; }
    case T_OUTS: return vouts(eval(env, t->a), eval(env, t->b), eval(env, t->c), eval(env, t->d));
    }
    return NULL;
}

/* ---- restriction to a face ---- */
static Env *restrict_env(Env *e, const Face *f) {
    if (!e) return NULL;
    Env *n = xalloc(sizeof *n); n->v = restrict_val(e->v, f); n->next = restrict_env(e->next, f); return n;
}
static void restrict_clo(Clo *dst, const Clo *src, const Face *f) {
    *dst = *src;
    if (src->fn) {
        Native *nt = src->data, *nn = xalloc(sizeof *nn); *nn = *nt; nn->cap = (VList){0};
        for (int i = 0; i < nt->cap.n; i++) vl_push(&nn->cap, restrict_val(nt->cap.a[i].v, f), nt->cap.a[i].irr);
        dst->data = nn;
    } else dst->env = restrict_env(src->env, f);
}
Val *restrict_val(Val *v, const Face *f) {
    if (!f || f->n == 0) return v;
    switch (v->k) {
    case V_U: case V_INTERVAL: return v;
    case V_I: return vi(iv_restrict(v->iv, f));
    case V_LAM: { Val *r = mkval(V_LAM); *r = *v; restrict_clo(&r->clo, &v->clo, f); return r; }
    case V_PI: { Val *r = mkval(V_PI); *r = *v; r->dom = restrict_val(v->dom, f); restrict_clo(&r->clo, &v->clo, f); return r; }
    case V_PATHP: { Val *r = mkval(V_PATHP); r->a = restrict_val(v->a, f); r->b = restrict_val(v->b, f); r->c = restrict_val(v->c, f); return r; }
    case V_PARTIAL: { Val *r = mkval(V_PARTIAL); r->a = restrict_val(v->a, f); r->b = restrict_val(v->b, f); return r; }
    case V_SUB: { Val *r = mkval(V_SUB); r->a = restrict_val(v->a, f); r->b = restrict_val(v->b, f); r->c = restrict_val(v->c, f); return r; }
    case V_INS: { Val *r = mkval(V_INS); r->a = restrict_val(v->a, f); return r; }
    case V_SYS: {
        VBranch *br = xalloc((v->nbr + 1) * sizeof(VBranch));
        for (int i = 0; i < v->nbr; i++) { br[i].phi = restrict_val(v->br[i].phi, f); br[i].v = restrict_val(v->br[i].v, f); }
        return vsys(br, v->nbr);
    }
    case V_DATA: case V_CON: {
        Val *r = mkval(v->k); r->n = v->n; r->args = (VList){0};
        for (int i = 0; i < v->args.n; i++) { Arg a = v->args.a[i]; a.v = restrict_val(a.v, f); if (a.papp) { a.x = restrict_val(a.x, f); a.y = restrict_val(a.y, f); } vl_push_arg(&r->args, a); }
        return r;
    }
    case V_NEU: {
        Val *head;
        switch (v->h) {
        case H_VAR: head = vvar(v->n); break;
        case H_ELIM: head = mkval(V_NEU); head->h = H_ELIM; head->n = v->n; break;
        case H_TRANSP: head = vtransp(restrict_val(v->a, f), restrict_val(v->b, f), restrict_val(v->c, f)); break;
        case H_HCOMP: head = vhcomp(restrict_val(v->a, f), restrict_val(v->b, f), restrict_val(v->c, f), restrict_val(v->dom, f)); break;
        case H_OUTS: head = vouts(restrict_val(v->a, f), restrict_val(v->b, f), restrict_val(v->c, f), restrict_val(v->dom, f)); break;
        default: die("internal: unknown neutral head");
        }
        for (int i = 0; i < v->args.n; i++) { Arg a = v->args.a[i]; a.v = restrict_val(a.v, f); if (a.papp) { a.x = restrict_val(a.x, f); a.y = restrict_val(a.y, f); } head = apply_arg(head, &a); }
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

static Val *proj_arg(Val *v, void *data) { int k = *(int *)data; if (v->k != V_CON && v->k != V_DATA) die("internal: projecting a non-constructor"); return v->args.a[k].v; }

static Val *native_apply(Native *nt, Val *arg) {
    switch (nt->code) {
    case N_IH: return ih_apply(nt, arg);
    case N_CONST: return CAP(nt, 0);
    case N_LINE_DOM: { Val *pi = vapp(CAP(nt, 0), arg, 0); if (pi->k != V_PI) die("internal: domain of a non-function line"); return pi->dom; }
    case N_LINE_COD_V: {    /* λi. B_i (v i), cap: line, vfn */
        Val *pi = vapp(CAP(nt, 0), arg, 0); if (pi->k != V_PI) die("internal: codomain of a non-function line");
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
    case N_HCOMP_PI_SIDES: return vapp(vapp(CAP(nt, 0), arg, 0), CAP(nt, 1), nt->i1);   /* λi. (u i) x */
    case N_PATH_HCOMP_SIDES: {   /* λi. [φ ↦ (u i) @ j, j ↦ y, ~j ↦ x], cap: u, phi, j, x, y */
        VBranch br[3];
        br[0].phi = CAP(nt, 1); br[0].v = vpapp(vapp(CAP(nt, 0), arg, 0), CAP(nt, 2), CAP(nt, 3), CAP(nt, 4));
        br[1].phi = CAP(nt, 2); br[1].v = CAP(nt, 4);
        br[2].phi = ineg(CAP(nt, 2)); br[2].v = CAP(nt, 3);
        return vsys(br, 3);
    }
    case N_LINE_PATH_AT: {       /* λi. (line i).line @ j  (the type of paths at i, applied to j), cap: line, j */
        Val *pt = vapp(CAP(nt, 0), arg, 0); if (pt->k != V_PATHP) die("internal: path line expected");
        return vapp(pt->a, CAP(nt, 1), 0);
    }
    case N_PATH_TRANSP_SIDES: {  /* λi. [φ ↦ p @ j, ~j ↦ x_i, j ↦ y_i], cap: line, phi, p, j */
        Val *pt = vapp(CAP(nt, 0), arg, 0); if (pt->k != V_PATHP) die("internal: path line expected");
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
        Con *C = &cons[nt->i1]; int np = datas[C->data].nparams;
        Val *Di = vapp(CAP(nt, 0), arg, 0); if (Di->k != V_DATA) die("internal: data line expected");
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
    case N_SYS_PROJ: {           /* λi. proj_k (u i) over the partial element; cap: u; i1 = k */
        Val *ui = vapp(CAP(nt, 0), arg, 0);
        int k = nt->i1;
        return vsys_map(ui, proj_arg, &k);
    }
    }
    die("internal: unknown native closure %d", nt->code);
    return NULL;
}

/* all branches of the partial element u (at a fresh i) are constructor c? */
static int sides_all_con(Val *u, int con) {
    Val *ui = vapp(u, fresh_ivar(), 0);
    if (ui->k == V_SYS) { for (int i = 0; i < ui->nbr; i++) if (ui->br[i].v->k != V_CON || ui->br[i].v->n != con) return 0; return 1; }
    return ui->k == V_CON && ui->n == con;
}

Val *vtransp(Val *line, Val *phi, Val *u0) {
    if (iv_is_one(phi->iv)) return u0;
    Val *fi = fresh_ivar();
    Val *Ai = vapp(line, fi, 0);
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
        typedef struct { Val *line, *phi, *f; int isi; } TP;
        TP *tp = xalloc(sizeof *tp); tp->line = line; tp->phi = phi; tp->f = u0; tp->isi = Ai->isi;
        extern Val *transp_pi_apply(void *, Val *);
        res->clo.fn = transp_pi_apply; res->clo.data = tp;
        return res;
    }
    case V_PATHP: {
        /* λj. comp (λi. A_i @ j) (φ ∨ j ∨ ~j) [φ ↦ p @ j, ~j ↦ x_i, j ↦ y_i] (p @ j) */
        typedef struct { Val *line, *phi, *p; } TPP;
        TPP *tp = xalloc(sizeof *tp); tp->line = line; tp->phi = phi; tp->p = u0;
        extern Val *transp_path_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "j"; res->isi = 1; res->clo.fn = transp_path_apply; res->clo.data = tp;
        return res;
    }
    case V_DATA: {
        Data *D = &datas[Ai->n];
        if (D->nparams + D->nidx == 0) return u0;
        if (u0->k != V_CON) return neu_transp(line, phi, u0);
        Con *C = &cons[u0->n];
        int np = D->nparams;
        /* transport each argument along its own line, with fillers for the earlier ones */
        Val **fills = xalloc((C->nargs + 1) * sizeof(Val *));
        Val *res = mkval(V_CON); res->n = u0->n;
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
    struct { Val *line, *phi, *f; int isi; } *tp = data;
    Val *v;
    if (tp->isi) v = vnative(N_CONST, 0, 0, 0, 1, u1);
    else v = vnative(N_TRANSP_V, 0, 0, 0, 3, vnative(N_LINE_DOM, 0, 0, 0, 1, tp->line), tp->phi, u1);
    Val *bline = vnative(N_LINE_COD_V, 0, 0, 0, 2, tp->line, v);
    return vtransp(bline, tp->phi, vapp(tp->f, vapp(v, izero(), 0), 0));
}
Val *transp_path_apply(void *data, Val *j) {
    struct { Val *line, *phi, *p; } *tp = data;
    Val *p0 = vapp(tp->line, izero(), 0);
    Val *aline = vnative(N_LINE_PATH_AT, 0, 0, 0, 2, tp->line, j);
    Val *sides = vnative(N_PATH_TRANSP_SIDES, 0, 0, 0, 4, tp->line, tp->phi, tp->p, j);
    return vcomp(aline, ior(tp->phi, ior(j, ineg(j))), sides, vpapp(tp->p, j, p0->b, p0->c));
}

Val *vhcomp(Val *A, Val *phi, Val *u, Val *u0) {
    if (iv_is_one(phi->iv)) { Val *t = vsys_at(vapp(u, ione(), 0), NULL); if (!t) die("internal: total system without a total branch"); return t; }
    switch (A->k) {
    case V_PI: {
        typedef struct { Val *A, *phi, *u, *u0; } HP;
        HP *hp = xalloc(sizeof *hp); hp->A = A; hp->phi = phi; hp->u = u; hp->u0 = u0;
        extern Val *hcomp_pi_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "x"; res->isi = A->isi; res->clo.fn = hcomp_pi_apply; res->clo.data = hp;
        return res;
    }
    case V_PATHP: {
        typedef struct { Val *A, *phi, *u, *u0; } HP;
        HP *hp = xalloc(sizeof *hp); hp->A = A; hp->phi = phi; hp->u = u; hp->u0 = u0;
        extern Val *hcomp_path_apply(void *, Val *);
        Val *res = mkval(V_LAM); res->name = "j"; res->isi = 1; res->clo.fn = hcomp_path_apply; res->clo.data = hp;
        return res;
    }
    case V_U: return neu_hcomp(A, phi, u, u0);      /* a normal form: formal composition in the universe */
    case V_DATA: {
        Data *D = &datas[A->n];
        if (D->nidx > 0) return neu_hcomp(A, phi, u, u0);
        if (u0->k != V_CON || !sides_all_con(u, u0->n)) return neu_hcomp(A, phi, u, u0);
        Con *C = &cons[u0->n]; int np = D->nparams;
        Val *res = mkval(V_CON); res->n = u0->n;
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
    struct { Val *A, *phi, *u, *u0; } *hp = data;
    Val *B = inst(&hp->A->clo, x);
    return vhcomp(B, hp->phi, vnative(N_HCOMP_PI_SIDES, hp->A->irr, 0, 0, 2, hp->u, x), vapp(hp->u0, x, hp->A->irr));
}
Val *hcomp_path_apply(void *data, Val *j) {
    struct { Val *A, *phi, *u, *u0; } *hp = data;
    Val *Aj = vapp(hp->A->a, j, 0);
    Val *sides = vnative(N_PATH_HCOMP_SIDES, 0, 0, 0, 5, hp->u, hp->phi, j, hp->A->b, hp->A->c);
    return vhcomp(Aj, ior(hp->phi, ior(j, ineg(j))), sides, vpapp(hp->u0, j, hp->A->b, hp->A->c));
}

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
Term *quote(int depth, Val *v) {
    switch (v->k) {
    case V_U: return mk_u(v->n);
    case V_INTERVAL: return mk(T_INTERVAL);
    case V_I: return quote_iv(depth, v->iv);
    case V_LAM: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        Term *t = mk_lam(v->name ? v->name : "x", quote(depth + 1, inst(&v->clo, x)), v->irr); t->isi = v->isi; return t;
    }
    case V_PI: {
        Val *x = v->isi ? vivar(depth) : vvar(depth);
        Term *t = mk_pi(v->name ? v->name : "_", quote(depth, v->dom), quote(depth + 1, inst(&v->clo, x)), v->irr); t->isi = v->isi; return t;
    }
    case V_PATHP: return mk_term(T_PATHP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
    case V_PARTIAL: return mk_term(T_PARTIAL, quote(depth, v->a), quote(depth, v->b), NULL, NULL);
    case V_SUB: return mk_term(T_SUB, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
    case V_INS: return mk_term(T_INS, quote(depth, v->a), NULL, NULL, NULL);
    case V_SYS: {
        Term *t = mk(T_SYS); t->nbr = v->nbr; t->br = xalloc((v->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < v->nbr; i++) { t->br[i].face = quote(depth, v->br[i].phi); t->br[i].body = quote(depth, v->br[i].v); }
        return t;
    }
    case V_NEU: case V_DATA: case V_CON: {
        Term *h;
        if (v->k == V_DATA) h = mk_ref(T_DATA, v->n);
        else if (v->k == V_CON) h = mk_ref(T_CON, v->n);
        else if (v->h == H_ELIM) h = mk_ref(T_ELIM, v->n);
        else if (v->h == H_TRANSP) h = mk_term(T_TRANSP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), NULL);
        else if (v->h == H_HCOMP) h = mk_term(T_HCOMP, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), quote(depth, v->dom));
        else if (v->h == H_OUTS) h = mk_term(T_OUTS, quote(depth, v->a), quote(depth, v->b), quote(depth, v->c), quote(depth, v->dom));
        else h = mk_var(depth - 1 - v->n);
        for (int i = 0; i < v->args.n; i++) {
            Arg *a = &v->args.a[i];
            if (a->papp) h = mk_term(T_PAPP, h, quote(depth, a->v), quote(depth, a->x), quote(depth, a->y));
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
        if (a->a[i].papp != b->a[i].papp) return 0;
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
int conv(int depth, Val *a, Val *b) {
    if (a == b) return 1;
    if (a->k == V_SYS || b->k == V_SYS) return conv_sys(depth, a, b);
    if (a->k == V_LAM || b->k == V_LAM) {          /* eta */
        int isi = (a->k == V_LAM ? a->isi : b->isi);
        Val *x = isi ? vivar(depth) : vvar(depth);
        Val *fa = a->k == V_LAM ? inst(&a->clo, x) : (isi ? vpapp(a, x, NULL, NULL) : vapp(a, x, 0));
        Val *fb = b->k == V_LAM ? inst(&b->clo, x) : (isi ? vpapp(b, x, NULL, NULL) : vapp(b, x, 0));
        return conv(depth + 1, fa, fb);
    }
    if (a->k != b->k) return 0;
    switch (a->k) {
    case V_U: return a->n == b->n;
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
    case V_NEU:
        if (a->h != b->h) return 0;
        if (a->h == H_TRANSP) { if (!(conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c))) return 0; }
        else if (a->h == H_HCOMP) { if (!(conv(depth, a->a, b->a) && conv(depth, a->b, b->b) && conv(depth, a->c, b->c) && conv(depth, a->dom, b->dom))) return 0; }
        else if (a->h == H_OUTS) { if (!conv(depth, a->dom, b->dom)) return 0; }
        else if (a->n != b->n) return 0;
        return conv_spine(depth, &a->args, &b->args);
    case V_DATA: case V_CON: return a->n == b->n && conv_spine(depth, &a->args, &b->args);
    default: return 0;
    }
}
