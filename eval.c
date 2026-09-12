/*
 * eval.c - core terms, values, normalization by evaluation, conversion.
 *
 * Terms use de Bruijn indices; values use de Bruijn levels for free
 * variables.  eval never fails on well-typed input; quote reads a value
 * back to a beta-normal, eta-long-for-functions term; conv compares values.
 * The only computation rule beyond beta is iota: an eliminator applied to
 * a constructor reduces to the constructor's method applied to the
 * constructor's arguments and the induction hypotheses.
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
Term *mk_pi(const char *x, Term *a, Term *b, int irr) { Term *t = mk(T_PI); t->name = x; t->a = a; t->b = b; t->irr = irr; return t; }
Term *mk_lam(const char *x, Term *body, int irr) { Term *t = mk(T_LAM); t->name = x; t->a = body; t->irr = irr; return t; }
Term *mk_app(Term *f, Term *a, int irr) { Term *t = mk(T_APP); t->a = f; t->b = a; t->irr = irr; return t; }
Term *mk_let(const char *x, Term *ty, Term *v, Term *body, int irr) { Term *t = mk(T_LET); t->name = x; t->a = ty; t->b = v; t->c = body; t->irr = irr; return t; }
Term *mk_ref(TKind k, int id) { Term *t = mk(k); t->n = id; return t; }

Term *shift2(Term *t, int cut1, int by1, int cut2, int by2) {
    if (!t) return NULL;
    switch (t->k) {
    case T_VAR:
        if (t->n >= cut2) return mk_var(t->n + by2);
        if (t->n >= cut1) return mk_var(t->n + by1);
        return t;
    case T_U: case T_DEF: case T_DATA: case T_CON: case T_ELIM: return t;
    case T_PI:  return mk_pi(t->name, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1 + 1, by1, cut2 + 1, by2), t->irr);
    case T_LAM: return mk_lam(t->name, shift2(t->a, cut1 + 1, by1, cut2 + 1, by2), t->irr);
    case T_APP: return mk_app(shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1, by1, cut2, by2), t->irr);
    case T_LET: return mk_let(t->name, shift2(t->a, cut1, by1, cut2, by2), shift2(t->b, cut1, by1, cut2, by2),
                              shift2(t->c, cut1 + 1, by1, cut2 + 1, by2), t->irr);
    }
    return t;
}
Term *shift(Term *t, int cut, int by) { return shift2(t, cut, by, cut, by); }

int term_eq(Term *a, Term *b) {
    if (a == b) return 1;
    if (!a || !b || a->k != b->k) return 0;
    switch (a->k) {
    case T_VAR: case T_U: case T_DEF: case T_DATA: case T_CON: case T_ELIM: return a->n == b->n;
    case T_PI:  return term_eq(a->a, b->a) && term_eq(a->b, b->b);
    case T_LAM: return term_eq(a->a, b->a);
    case T_APP: return term_eq(a->a, b->a) && term_eq(a->b, b->b);
    case T_LET: return term_eq(a->a, b->a) && term_eq(a->b, b->b) && term_eq(a->c, b->c);
    }
    return 0;
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
    case T_APP:
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
    }
}
void term_print(FILE *f, Term *t, const char **names, int depth) { tp(f, t, names, depth, 0); }

/* ---- values ---- */
void vl_push(VList *l, Val *v) {
    if (l->n == l->cap) { int c = l->cap ? 2 * l->cap : 4; Val **nv = xalloc(c * sizeof(Val *)); if (l->n) memcpy(nv, l->v, l->n * sizeof(Val *)); l->v = nv; l->cap = c; }
    l->v[l->n++] = v;
}
VList vl_copy(const VList *l) { VList r = {0}; for (int i = 0; i < l->n; i++) vl_push(&r, l->v[i]); return r; }
Env *env_push(Env *e, Val *v) { Env *n = xalloc(sizeof *n); n->v = v; n->next = e; return n; }
Val *env_get(Env *e, int idx) { while (idx-- > 0) { if (!e) die("internal: unbound variable"); e = e->next; } if (!e) die("internal: unbound variable"); return e->v; }

static Val *mkv(VKind k) { Val *v = xalloc(sizeof *v); v->k = k; return v; }
Val *vvar(int level) { Val *v = mkv(V_NEU); v->h = H_VAR; v->n = level; return v; }
Val *vu(int l) { Val *v = mkv(V_U); v->n = l; return v; }

/* induction-hypothesis closures: \y_1..y_q -> elim D params P methods idx[y] (a y_1..y_q) */
struct IhClo {
    int data; VList base;      /* params, motive, methods */
    Env *tele;                 /* environment for the index terms: params, previous constructor args */
    Con *con; int j;           /* which constructor argument */
    VList ys; Val *aj;
};
static Val *elim_apply_list(int data, VList *args);
static Val *ih_apply(IhClo *c, Val *y) {
    IhClo *d = xalloc(sizeof *d); *d = *c; d->ys = vl_copy(&c->ys); vl_push(&d->ys, y);
    ConArg *ca = &c->con->args[c->j];
    if (d->ys.n < ca->npi) { Val *v = mkv(V_LAM); v->clo.ih = d; v->name = "y"; return v; }
    Env *e = d->tele; for (int i = 0; i < d->ys.n; i++) e = env_push(e, d->ys.v[i]);
    VList args = vl_copy(&d->base);
    for (int i = 0; i < ca->nidx; i++) vl_push(&args, eval(e, ca->idx[i]));
    Val *t = d->aj; for (int i = 0; i < d->ys.n; i++) t = vapp(t, d->ys.v[i], 0);
    vl_push(&args, t);
    return elim_apply_list(d->data, &args);
}

Val *inst(Clo *c, Val *v) {
    if (c->ih) return ih_apply(c->ih, v);
    return eval(env_push(c->env, v), c->t);
}

static Val *neu_app(Val *f, Val *a, int irr) {
    Val *v = mkv(f->k); *v = *f; v->args = vl_copy(&f->args); a->irr = irr; vl_push(&v->args, a); return v;
}

/* iota: the eliminator's full spine ends in a constructor */
static Val *elim_reduce(int data, VList *args) {
    Data *D = &datas[data];
    int np = D->nparams, k = D->ncons;
    Val *target = args->v[args->n - 1];
    if (target->k != V_CON) return NULL;
    Con *c = &cons[target->n];
    if (c->data != data || target->args.n != np + c->nargs) return NULL;
    Val *res = args->v[np + 1 + c->ci];
    Env *tele = NULL; for (int i = 0; i < np; i++) tele = env_push(tele, target->args.v[i]);
    for (int j = 0; j < c->nargs; j++) res = vapp(res, target->args.v[np + j], c->args[j].irr);
    for (int j = 0; j < c->nargs; j++) {
        if (!c->args[j].isrec) continue;
        IhClo *ih = xalloc(sizeof *ih);
        ih->data = data; ih->con = c; ih->j = j; ih->aj = target->args.v[np + j];
        for (int i = 0; i < np + 1 + k; i++) vl_push(&ih->base, args->v[i]);
        Env *e = tele; for (int i = 0; i < j; i++) e = env_push(e, target->args.v[np + i]);
        ih->tele = e;
        Val *ihv;
        if (c->args[j].npi == 0) {
            VList a2 = vl_copy(&ih->base);
            for (int i = 0; i < c->args[j].nidx; i++) vl_push(&a2, eval(e, c->args[j].idx[i]));
            vl_push(&a2, ih->aj);
            ihv = elim_apply_list(data, &a2);
        } else { ihv = mkv(V_LAM); ihv->clo.ih = ih; ihv->name = "y"; }
        res = vapp(res, ihv, 0);
    }
    return res;
}
static Val *elim_apply_list(int data, VList *args) {
    Val *e = mkv(V_NEU); e->h = H_ELIM; e->n = data;
    Val *r = e;
    for (int i = 0; i < args->n; i++) r = vapp(r, args->v[i], args->v[i]->irr);
    return r;
}

Val *vapp(Val *f, Val *a, int irr) {
    switch (f->k) {
    case V_LAM: return inst(&f->clo, a);
    case V_NEU:
        if (f->h == H_ELIM) {
            Val *v = neu_app(f, a, irr);
            Data *D = &datas[f->n];
            int arity = D->nparams + 1 + D->ncons + D->nidx + 1;
            if (v->args.n == arity) { Val *r = elim_reduce(f->n, &v->args); if (r) return r; }
            return v;
        }
        return neu_app(f, a, irr);
    case V_DATA: case V_CON: return neu_app(f, a, irr);
    default: die("internal: application of a non-function value");
    }
    return NULL;
}

Val *eval(Env *env, Term *t) {
    switch (t->k) {
    case T_VAR: return env_get(env, t->n);
    case T_U: return vu(t->n);
    case T_PI: { Val *v = mkv(V_PI); v->name = t->name; v->irr = t->irr; v->dom = eval(env, t->a); v->clo.env = env; v->clo.t = t->b; return v; }
    case T_LAM: { Val *v = mkv(V_LAM); v->name = t->name; v->irr = t->irr; v->clo.env = env; v->clo.t = t->a; return v; }
    case T_APP: return vapp(eval(env, t->a), eval(env, t->b), t->irr);
    case T_LET: return eval(env_push(env, eval(env, t->b)), t->c);
    case T_DEF: return defs[t->n].vval;
    case T_DATA: { Val *v = mkv(V_DATA); v->n = t->n; return v; }
    case T_CON: { Val *v = mkv(V_CON); v->n = t->n; return v; }
    case T_ELIM: { Val *v = mkv(V_NEU); v->h = H_ELIM; v->n = t->n; return v; }
    }
    return NULL;
}

Term *quote(int depth, Val *v) {
    switch (v->k) {
    case V_U: return mk_u(v->n);
    case V_LAM: return mk_lam(v->name ? v->name : "x", quote(depth + 1, inst(&v->clo, vvar(depth))), v->irr);
    case V_PI: return mk_pi(v->name ? v->name : "_", quote(depth, v->dom), quote(depth + 1, inst(&v->clo, vvar(depth))), v->irr);
    case V_NEU: case V_DATA: case V_CON: {
        Term *h;
        if (v->k == V_DATA) h = mk_ref(T_DATA, v->n);
        else if (v->k == V_CON) h = mk_ref(T_CON, v->n);
        else if (v->h == H_ELIM) h = mk_ref(T_ELIM, v->n);
        else h = mk_var(depth - 1 - v->n);
        for (int i = 0; i < v->args.n; i++) h = mk_app(h, quote(depth, v->args.v[i]), v->args.v[i]->irr);
        return h;
    }
    }
    return NULL;
}

static int conv_spine(int depth, VList *a, VList *b) {
    if (a->n != b->n) return 0;
    for (int i = 0; i < a->n; i++) if (!conv(depth, a->v[i], b->v[i])) return 0;
    return 1;
}
int conv(int depth, Val *a, Val *b) {
    if (a == b) return 1;
    if (a->k == V_LAM || b->k == V_LAM) {          /* eta */
        Val *x = vvar(depth);
        return conv(depth + 1, vapp(a, x, 0), vapp(b, x, 0));
    }
    if (a->k != b->k) return 0;
    switch (a->k) {
    case V_U: return a->n == b->n;
    case V_PI: return conv(depth, a->dom, b->dom) && conv(depth + 1, inst(&a->clo, vvar(depth)), inst(&b->clo, vvar(depth)));
    case V_NEU: return a->h == b->h && a->n == b->n && conv_spine(depth, &a->args, &b->args);
    case V_DATA: case V_CON: return a->n == b->n && conv_spine(depth, &a->args, &b->args);
    default: return 0;
    }
}
