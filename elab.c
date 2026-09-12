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
 */
#include "tt.h"

typedef struct { const char **names; Val **tys; int n, cap; Env *env; } Ctx;

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
static void ctx_bind(Ctx *c, const char *name, Val *ty) { ctx_push(c, name, ty, vvar(c->n)); }

static int find_def(const char *n) { for (int i = ndefs - 1; i >= 0; i--) if (!strcmp(defs[i].name, n)) return i; return -1; }
static int find_data(const char *n) { for (int i = ndatas - 1; i >= 0; i--) if (!strcmp(datas[i].name, n)) return i; return -1; }
static int find_con(const char *n) { for (int i = ncons - 1; i >= 0; i--) if (!strcmp(cons[i].name, n)) return i; return -1; }
static void check_fresh(const char *n, int line) {
    if (find_def(n) >= 0 || find_data(n) >= 0 || find_con(n) >= 0) die("line %d: '%s' is already defined", line, n);
}

static int term_binders(Term *t) {
    if (!t) return 0;
    int a = term_binders(t->a), b = term_binders(t->b), c = term_binders(t->c);
    int m = a > b ? a : b; if (c > m) m = c;
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
    if (ty->k == V_U) return 1;
    if (ty->k == V_PI) return is_type_like(depth + 1, inst(&ty->clo, vvar(depth)));
    return 0;
}

static Term *infer(Ctx *c, STerm *s, Val **ty);
static Term *check(Ctx *c, STerm *s, Val *ty);

/* a term must be a type: returns its core and universe level */
static Term *check_type(Ctx *c, STerm *s, int *lvl) {
    Val *ty; Term *t = infer(c, s, &ty);
    if (ty->k != V_U) die("line %d: expected a type, but %s : %s", s->line, "the term", show(c, ty));
    *lvl = ty->n; return t;
}

/* ---- induction principles ---- */

/* D p i, under a context where params start at index pbase (p_t = pbase + np-1-t) and indices at index ibase (i_j = ibase + m-1-j) */
static Term *data_applied(int d, int pbase, int ibase) {
    Data *D = &datas[d]; Term *t = mk_ref(T_DATA, d);
    for (int i = 0; i < D->nparams; i++) t = mk_app(t, mk_var(pbase + D->nparams - 1 - i), 1);
    for (int j = 0; j < D->nidx; j++) t = mk_app(t, mk_var(ibase + D->nidx - 1 - j), 1);
    return t;
}

/* closed type of  elim D  for a motive into U lvl; res_irr says the motive's fibres are themselves types */
static Term *elim_type(int d, int lvl, int res_irr) {
    Data *D = &datas[d];
    int np = D->nparams, m = D->nidx, k = D->ncons;
    /* body: P i x   under [params, P, mth(k), i(m), x] */
    Term *body = mk_var(1 + m + k);
    for (int j = 0; j < m; j++) body = mk_app(body, mk_var(1 + (m - 1 - j)), 1);
    body = mk_app(body, mk_var(0), 0);
    /* x : D p i */
    Term *t = mk_pi("x", data_applied(d, m + k + 1, 0), body, 0);
    for (int j = m - 1; j >= 0; j--) t = mk_pi(xsprintf("i%d", j), shift(D->itys[j], j, k + 1), t, 1);
    /* methods */
    for (int ci = k - 1; ci >= 0; ci--) {
        Con *C = &cons[D->cons[ci]]; int r = C->nargs, htot = C->nrec;
        /* return: P ridx (c p a)   under [params, P, mth(ci), a(r), ih(htot)] */
        Term *ret = mk_var(ci + r + htot);
        for (int j = 0; j < m; j++) ret = mk_app(ret, shift2(C->ridx[j], 0, htot, r, htot + ci + 1), 1);
        Term *ct = mk_ref(T_CON, D->cons[ci]);
        for (int i = 0; i < np; i++) ct = mk_app(ct, mk_var(htot + r + ci + 1 + (np - 1 - i)), 1);
        for (int j = 0; j < r; j++) ct = mk_app(ct, mk_var(htot + (r - 1 - j)), C->args[j].irr);
        ret = mk_app(ret, ct, 0);
        Term *mt = ret;
        /* induction hypotheses, last first */
        int h = htot;
        for (int j = r - 1; j >= 0; j--) {
            ConArg *A = &C->args[j];
            if (!A->isrec) continue;
            h--;
            int q = A->npi;
            /* P idx[y] (a_j y..)   under [params, P, mth(ci), a(r), ih(h), y(q)] */
            Term *ih = mk_var(ci + r + h + q);
            for (int i = 0; i < A->nidx; i++) ih = mk_app(ih, shift2(A->idx[i], q, h + (r - j), q + j, h + (r - j) + ci + 1), 1);
            Term *aj = mk_var((r - 1 - j) + h + q);
            Term *aty = A->ty; int yt = 1;
            for (Term *w = aty; w->k == T_PI && yt <= q; w = w->b, yt++) aj = mk_app(aj, mk_var(q - yt), w->irr);
            ih = mk_app(ih, aj, 0);
            /* wrap the y binders, innermost first */
            Term **ys = xalloc((q + 1) * sizeof(Term *)); int *yirr = xalloc((q + 1) * sizeof(int));
            { Term *w = aty; for (int tt = 0; tt < q; tt++) { ys[tt] = w->a; yirr[tt] = w->irr; w = w->b; } }
            for (int tt = q - 1; tt >= 0; tt--)
                ih = mk_pi(xsprintf("y%d", tt), shift2(ys[tt], tt, h + (r - j), tt + j, h + (r - j) + ci + 1), ih, yirr[tt]);
            mt = mk_pi(xsprintf("ih%d", j), ih, mt, res_irr);
        }
        for (int j = r - 1; j >= 0; j--) mt = mk_pi(C->args[j].name, shift(C->args[j].ty, j, ci + 1), mt, C->args[j].irr);
        t = mk_pi(xsprintf("m_%s", C->name), mt, t, 0);
    }
    /* motive: (i..) -> D p i -> U lvl   under [params] */
    Term *P = mk_pi("x", data_applied(d, m, 0), mk_u(lvl), 0);
    for (int j = m - 1; j >= 0; j--) P = mk_pi(xsprintf("i%d", j), D->itys[j], P, 1);
    t = mk_pi("P", P, t, 1);
    for (int i = np - 1; i >= 0; i--) t = mk_pi(xsprintf("p%d", i), D->ptys[i], t, 1);
    return t;
}

/* ---- applications ---- */

static Term *app_spine(Ctx *c, STerm *s, STerm **args, int nargs, Term *head, Val *hty, Val **ty) {
    for (int i = 0; i < nargs; i++) {
        if (hty->k != V_PI) die("line %d: applying a non-function of type %s", args[i]->line, show(c, hty));
        Term *a = check(c, args[i], hty->dom);
        head = mk_app(head, a, hty->irr);
        hty = inst(&hty->clo, eval(c->env, a));
    }
    (void)s; *ty = hty; return head;
}

static Term *infer_app(Ctx *c, STerm *s, Val **ty) {
    STerm **args = NULL; int n = 0, cap = 0;
    STerm *h = s;
    while (h->k == S_APP) {
        if (n == cap) { cap = cap ? 2 * cap : 8; STerm **na = xalloc(cap * sizeof(STerm *)); if (n) memcpy(na, args, n * sizeof(STerm *)); args = na; }
        args[n++] = h->b; h = h->a;
    }
    for (int i = 0; i < n / 2; i++) { STerm *t = args[i]; args[i] = args[n - 1 - i]; args[n - 1 - i] = t; }
    if (h->k == S_ELIM) {
        int d = find_data(h->name);
        if (d < 0) die("line %d: elim of unknown data type '%s'", h->line, h->name);
        Data *D = &datas[d]; int np = D->nparams, m = D->nidx;
        if (n < np + 1) die("line %d: elim %s needs its %d parameter%s and a motive", h->line, D->name, np, np == 1 ? "" : "s");
        /* parameters */
        Env *pe = NULL; Val **pv = xalloc((np + 1) * sizeof(Val *));
        for (int i = 0; i < np; i++) {
            Term *p = check(c, args[i], eval(pe, D->ptys[i]));
            pv[i] = eval(c->env, p); pe = env_push(pe, pv[i]);
        }
        /* motive: peel its lambdas against the expected binders (indices, then the target),
           then read the universe of what remains */
        int lvl, res_irr;
        {
            STerm *ms = args[np]; Env *ie = pe; int nb = 0, depth = c->n;
            Val **iv = xalloc((m + 2) * sizeof(Val *));
            #define TARGET_TYPE(dst) do { \
                Val *dv_ = xalloc(sizeof *dv_); dv_->k = V_DATA; dv_->n = d; \
                for (int i_ = 0; i_ < np; i_++) { vl_push(&dv_->args, pv[i_]); } \
                for (int j_ = 0; j_ < m; j_++) { vl_push(&dv_->args, iv[j_]); } \
                (dst) = dv_; } while (0)
            while (nb <= m && ms->k == S_LAM) {
                Val *dom;
                if (nb < m) dom = eval(ie, D->itys[nb]); else TARGET_TYPE(dom);
                ctx_bind(c, ms->binders[0].name, dom);
                Val *x = vvar(c->n - 1); depth = c->n;
                if (nb < m) { iv[nb] = x; ie = env_push(ie, x); }
                ms = ms->a; nb++;
            }
            Val *rty; Term *rt = infer(c, ms, &rty);
            Val *cur = rty;
            for (int j = nb; j <= m; j++) {
                if (cur->k != V_PI) die("line %d: motive for %s must abstract over %d index%s and the target", ms->line, D->name, m, m == 1 ? "" : "es");
                Val *dom;
                if (j < m) dom = eval(ie, D->itys[j]); else TARGET_TYPE(dom);
                expect_conv(c, ms->line, cur->dom, dom, "motive binder");
                Val *x = vvar(depth++);
                if (j < m) { iv[j] = x; ie = env_push(ie, x); }
                cur = inst(&cur->clo, x);
            }
            #undef TARGET_TYPE
            if (cur->k != V_U) die("line %d: motive for %s must land in a universe, not %s", ms->line, D->name, show(c, cur));
            lvl = cur->n;
            Val *fib = eval(c->env, rt);
            for (int j = nb; j <= m; j++) fib = vapp(fib, vvar(c->n + (j - nb)), 0);
            res_irr = is_type_like(c->n + (m + 1 - nb), fib);
            for (int i = 0; i < nb; i++) ctx_pop(c);
        }
        Term *ety = elim_type(d, lvl, res_irr);
        return app_spine(c, s, args, n, mk_ref(T_ELIM, d), eval(NULL, ety), ty);
    }
    Val *hty; Term *head = infer(c, h, &hty);
    return app_spine(c, s, args, n, head, hty, ty);
}

/* ---- terms ---- */

static Term *infer(Ctx *c, STerm *s, Val **ty) {
    switch (s->k) {
    case S_VAR: {
        for (int i = c->n - 1; i >= 0; i--)
            if (!strcmp(c->names[i], s->name)) { *ty = c->tys[i]; return mk_var(c->n - 1 - i); }
        int id;
        if ((id = find_con(s->name)) >= 0) { *ty = eval(NULL, cons[id].ty); return mk_ref(T_CON, id); }
        if ((id = find_def(s->name)) >= 0) { *ty = defs[id].vty; return mk_ref(T_DEF, id); }
        if ((id = find_data(s->name)) >= 0) { *ty = eval(NULL, datas[id].ty); return mk_ref(T_DATA, id); }
        die("line %d: unbound name '%s'", s->line, s->name);
    }
    case S_U: *ty = vu(s->lvl + 1); return mk_u(s->lvl);
    case S_PI: {
        SBinder *b = &s->binders[0];
        int la, lb; Term *dom = check_type(c, b->ty, &la);
        Val *dv = eval(c->env, dom); int irr = is_type_like(c->n, dv);
        ctx_bind(c, b->name, dv);
        Term *cod = check_type(c, s->a, &lb);
        ctx_pop(c);
        *ty = vu(la > lb ? la : lb);
        return mk_pi(b->name, dom, cod, irr);
    }
    case S_LAM: die("line %d: cannot infer the type of a lambda; add an annotation", s->line);
    case S_APP: return infer_app(c, s, ty);
    case S_LET: {
        int l; Term *tyt = check_type(c, s->a, &l);
        Val *tv = eval(c->env, tyt);
        Term *v = check(c, s->b, tv);
        int irr = is_type_like(c->n, tv);
        ctx_push(c, s->name, tv, eval(c->env, v));
        Val *bty; Term *body = infer(c, s->c, &bty);
        ctx_pop(c);
        *ty = bty;
        return mk_let(s->name, tyt, v, body, irr);
    }
    case S_ELIM: return infer_app(c, s, ty);
    }
    return NULL;
}

static Term *check(Ctx *c, STerm *s, Val *ty) {
    if (s->k == S_LAM) {
        if (ty->k != V_PI) die("line %d: lambda checked against non-function type %s", s->line, show(c, ty));
        SBinder *b = &s->binders[0];
        ctx_bind(c, b->name, ty->dom);
        Term *body = check(c, s->a, inst(&ty->clo, vvar(c->n - 1)));
        ctx_pop(c);
        return mk_lam(b->name, body, ty->irr);
    }
    if (s->k == S_LET) {
        int l; Term *tyt = check_type(c, s->a, &l);
        Val *tv = eval(c->env, tyt);
        Term *v = check(c, s->b, tv);
        int irr = is_type_like(c->n, tv);
        ctx_push(c, s->name, tv, eval(c->env, v));
        Term *body = check(c, s->c, ty);
        ctx_pop(c);
        return mk_let(s->name, tyt, v, body, irr);
    }
    Val *got; Term *t = infer(c, s, &got);
    if (got->k == V_U && ty->k == V_U && got->n <= ty->n) return t;   /* cumulativity */
    if (!conv(c->n, got, ty)) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
    return t;
}

/* ---- declarations ---- */

static int mentions(Term *t, int d) {
    if (!t) return 0;
    switch (t->k) {
    case T_DATA: return t->n == d;
    case T_PI: return mentions(t->a, d) || mentions(t->b, d);
    case T_LAM: return mentions(t->a, d);
    case T_APP: return mentions(t->a, d) || mentions(t->b, d);
    case T_LET: return mentions(t->a, d) || mentions(t->b, d) || mentions(t->c, d);
    default: return 0;
    }
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

static void elab_data(SDecl *s) {
    check_fresh(s->name, s->line);
    Ctx c = {0};
    Data D = {0}; D.name = s->name; D.line = s->line; D.nparams = s->nparams;
    D.ptys = xalloc((s->nparams + 1) * sizeof(Term *));
    for (int i = 0; i < s->nparams; i++) {
        int l; D.ptys[i] = check_type(&c, s->params[i].ty, &l);
        ctx_bind(&c, s->params[i].name, eval(c.env, D.ptys[i]));
    }
    int l; Term *ity = check_type(&c, s->ty, &l);
    Term *w = ity; int m = 0;
    for (Term *x = ity; x->k == T_PI; x = x->b) m++;
    D.nidx = m; D.itys = xalloc((m + 1) * sizeof(Term *));
    for (int j = 0; j < m; j++) { D.itys[j] = w->a; w = w->b; }
    if (w->k != T_U) die("line %d: the type of data %s must end in a universe", s->line, s->name);
    D.lvl = w->n;
    Term *full = ity;
    for (int i = s->nparams - 1; i >= 0; i--) full = mk_pi(s->params[i].name, D.ptys[i], full, 1);
    { Term *x = ity; for (int j = 0; j < m; j++) { x->irr = 1; x = x->b; } }
    D.ty = full;
    int d = ndatas;
    datas = realloc(datas, (ndatas + 1) * sizeof(Data)); if (!datas) die("out of memory");
    datas[ndatas++] = D;
    /* constructors, one at a time so that later ones may not depend on earlier ones' names (they are constants anyway) */
    for (int ci = 0; ci < s->ncons; ci++) {
        SCon *sc = &s->cons[ci];
        check_fresh(sc->name, sc->line);
        int lc; Term *cty = check_type(&c, sc->ty, &lc);
        if (lc > D.lvl) die("line %d: constructor %s : %s lives in U %d, above data %s : U %d", sc->line, sc->name, "its type", lc, s->name, D.lvl);
        Con C = {0}; C.name = sc->name; C.data = d; C.ci = ci; C.line = sc->line;
        int r = 0; for (Term *x = cty; x->k == T_PI; x = x->b) r++;
        C.args = xalloc((r + 1) * sizeof(ConArg)); C.nargs = r;
        Term *x = cty;
        for (int j = 0; j < r; j++) {
            ConArg *A = &C.args[j];
            A->name = x->name; A->ty = x->a; A->irr = x->irr;
            /* strict positivity */
            Term *y = A->ty; int q = 0;
            while (y->k == T_PI) {
                if (mentions(y->a, d)) die("line %d: constructor %s is not strictly positive in %s", sc->line, sc->name, s->name);
                y = y->b; q++;
            }
            Term **idx; int nidx;
            if (mentions(y, d)) {
                if (!data_spine(y, d, q + j, &idx, &nidx)) die("line %d: constructor %s is not strictly positive in %s", sc->line, sc->name, s->name);
                A->isrec = 1; A->npi = q; A->idx = idx; A->nidx = nidx; C.nrec++;
            }
            x = x->b;
        }
        Term **ridx; int nridx;
        if (!data_spine(x, d, r, &ridx, &nridx)) die("line %d: constructor %s must return %s", sc->line, sc->name, s->name);
        C.ridx = ridx;
        Term *closed = cty;
        for (int i = s->nparams - 1; i >= 0; i--) closed = mk_pi(s->params[i].name, D.ptys[i], closed, 1);
        C.ty = closed;
        int cid = ncons;
        cons = realloc(cons, (ncons + 1) * sizeof(Con)); if (!cons) die("out of memory");
        cons[ncons++] = C;
        Data *DD = &datas[d];
        DD->cons = realloc(DD->cons, (DD->ncons + 1) * sizeof(int)); if (!DD->cons) die("out of memory");
        DD->cons[DD->ncons++] = cid;
    }
}

static void elab_def(SDecl *s) {
    check_fresh(s->name, s->line);
    Ctx c = {0};
    int l; Term *ty = check_type(&c, s->ty, &l);
    Val *vty = eval(NULL, ty);
    Term *val = check(&c, s->val, vty);
    Def D = {0}; D.name = s->name; D.ty = ty; D.val = val; D.vty = vty; D.vval = eval(NULL, val); D.irr = is_type_like(0, vty); D.line = s->line;
    defs = realloc(defs, (ndefs + 1) * sizeof(Def)); if (!defs) die("out of memory");
    defs[ndefs++] = D;
}

void elab_program(SDecl *decls) {
    for (SDecl *s = decls; s; s = s->next) {
        if (s->isdata) elab_data(s); else elab_def(s);
    }
}
