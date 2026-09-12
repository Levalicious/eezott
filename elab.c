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
static void ctx_bind_i(Ctx *c, const char *name) { ctx_push(c, name, mkval(V_INTERVAL), vivar(c->n)); }

/* the context restricted to a face: types and environment values re-evaluated with the face's endpoints */
static Ctx ctx_restrict(Ctx *c, const Face *f) {
    Ctx r = {0}; r.n = c->n; r.cap = c->n;
    r.names = xalloc((c->n + 1) * sizeof(char *)); r.tys = xalloc((c->n + 1) * sizeof(Val *));
    Val **vs = xalloc((c->n + 1) * sizeof(Val *));
    for (int i = 0; i < c->n; i++) { r.names[i] = c->names[i]; r.tys[i] = restrict_val(c->tys[i], f); vs[c->n - 1 - i] = env_get(c->env, i); }
    for (int i = 0; i < c->n; i++) r.env = env_push(r.env, restrict_val(vs[i], f));
    return r;
}

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
    case V_U: return 1;
    case V_PI: return is_type_like(depth + 1, inst(&ty->clo, ty->isi ? vivar(depth) : vvar(depth)));
    case V_PATHP: return is_type_like(depth + 1, vapp(ty->a, vivar(depth), 0));
    case V_PARTIAL: return is_type_like(depth, ty->b);
    case V_SUB: return is_type_like(depth, ty->a);
    default: return 0;
    }
}

static Term *infer(Ctx *c, STerm *s, Val **ty);
static Term *check(Ctx *c, STerm *s, Val *ty);

/* a term must be a type: returns its core and universe level */
static Term *check_type(Ctx *c, STerm *s, int *lvl) {
    Val *ty; Term *t = infer(c, s, &ty);
    if (ty->k != V_U) die("line %d: expected a type, but %s : %s", s->line, "the term", show(c, ty));
    *lvl = ty->n; return t;
}
/* a line of types  (i : I) -> U l : either a lambda over an interval variable, or a term whose type is such a function */
static Term *check_line(Ctx *c, STerm *s, int *lvl) {
    if (s->k == S_LAM) {
        ctx_bind_i(c, s->binders[0].name);
        Term *body = check_type(c, s->a, lvl);
        ctx_pop(c);
        Term *t = mk_lam(s->binders[0].name, body, 0); t->isi = 1; return t;
    }
    Val *ty; Term *t = infer(c, s, &ty);
    if (ty->k != V_PI || !ty->isi) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
    Val *cod = inst(&ty->clo, vivar(c->n));
    if (cod->k != V_U) die("line %d: expected a line of types (i : I) -> U, but the term has type %s", s->line, show(c, ty));
    *lvl = cod->n; return t;
}
static Val *vinterval(void) { return mkval(V_INTERVAL); }
static Term *check_interval(Ctx *c, STerm *s) { return check(c, s, vinterval()); }

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

static Term *app_spine(Ctx *c, STerm **args, int nargs, Term *head, Val *hty, Val **ty) {
    for (int i = 0; i < nargs; i++) {
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
                Val *dv_ = mkval(V_DATA); dv_->n = d; \
                for (int i_ = 0; i_ < np; i_++) { vl_push(&dv_->args, pv[i_], 1); } \
                for (int j_ = 0; j_ < m; j_++) { vl_push(&dv_->args, iv[j_], 1); } \
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
            (void)fib; res_irr = 0;
            for (int i = 0; i < nb; i++) ctx_pop(c);
        }
        Term *ety = elim_type(d, lvl, res_irr);
        return app_spine(c, args, n, mk_ref(T_ELIM, d), eval(NULL, ety), ty);
    }
    case S_PATHP: {
        int lvl; Term *line, *x, *y;
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
        return app_spine(c, args + 3, n - 3, mk_term(T_PATHP, line, x, y, NULL), vu(lvl), ty);
    }
    case S_PARTIAL: {
        need_args(h, n, 2, "Partial");
        Term *phi = check_interval(c, args[0]);
        int lvl; Term *A = check_type(c, args[1], &lvl);
        return app_spine(c, args + 2, n - 2, mk_term(T_PARTIAL, phi, A, NULL, NULL), vu(lvl), ty);
    }
    case S_TRANSP: {
        need_args(h, n, 3, "transp");
        int lvl; Term *line = check_line(c, args[0], &lvl);
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
        int lvl; Term *A = check_type(c, args[0], &lvl); Val *Av = eval(c->env, A);
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
        int lvl; Term *line = check_line(c, args[0], &lvl); Val *lv = eval(c->env, line);
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
        int lvl; Term *A = check_type(c, args[0], &lvl); Val *Av = eval(c->env, A);
        Term *phi = check_interval(c, args[1]); Val *pv = eval(c->env, phi);
        Val *pty = mkval(V_PARTIAL); pty->a = pv; pty->b = Av;
        Term *u = check(c, args[2], pty);
        return app_spine(c, args + 3, n - 3, mk_term(T_SUB, A, phi, u, NULL), vu(lvl), ty);
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

static Term *check_system(Ctx *c, STerm *s, Val *ty) {
    if (ty->k != V_PARTIAL) die("line %d: a system must be checked against a Partial type, not %s", s->line, show(c, ty));
    Val *phi = ty->a, *A = ty->b;
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
            Term *b = check(&rc, s->br[k].body, restrict_val(A, &fs[i]));
            if (!body) body = b;
        }
        t->br[k].body = body; bv[k] = eval(c->env, body);
    }
    /* overlapping branches must agree */
    for (int k = 0; k < s->nbr; k++) for (int l = k + 1; l < s->nbr; l++) {
        Face *fs; int nf = faces_of(vi(iv_and(psi[k]->iv, psi[l]->iv)), &fs);
        for (int i = 0; i < nf; i++)
            if (!conv(c->n, restrict_val(bv[k], &fs[i]), restrict_val(bv[l], &fs[i])))
                die("line %d: system branches %d and %d disagree where their faces overlap", s->line, k + 1, l + 1);
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
        if ((id = find_con(s->name)) >= 0) { *ty = eval(NULL, cons[id].ty); return mk_ref(T_CON, id); }
        if ((id = find_def(s->name)) >= 0) { *ty = defs[id].vty; return mk_ref(T_DEF, id); }
        if ((id = find_data(s->name)) >= 0) { *ty = eval(NULL, datas[id].ty); return mk_ref(T_DATA, id); }
        die("line %d: unbound name '%s'", s->line, s->name);
    }
    case S_U: *ty = vu(s->lvl + 1); return mk_u(s->lvl);
    case S_I: die("line %d: I is the type of interval variables; it is not itself a term of a universe", s->line);
    case S_I0: *ty = vinterval(); return mk_term(T_I0, NULL, NULL, NULL, NULL);
    case S_I1: *ty = vinterval(); return mk_term(T_I1, NULL, NULL, NULL, NULL);
    case S_IAND: case S_IOR: {
        Term *a = check_interval(c, s->a), *b = check_interval(c, s->b);
        *ty = vinterval(); return mk_term(s->k == S_IAND ? T_IAND : T_IOR, a, b, NULL, NULL);
    }
    case S_INEG: { Term *a = check_interval(c, s->a); *ty = vinterval(); return mk_term(T_INEG, a, NULL, NULL, NULL); }
    case S_PI: {
        SBinder *b = &s->binders[0];
        if (b->ty->k == S_I) {
            ctx_bind_i(c, b->name);
            int lb; Term *cod = check_type(c, s->a, &lb);
            ctx_pop(c);
            *ty = vu(lb);
            Term *t = mk_pi(b->name, mk_term(T_INTERVAL, NULL, NULL, NULL, NULL), cod, 0); return t;
        }
        int la, lb; Term *dom = check_type(c, b->ty, &la);
        Val *dv = eval(c->env, dom); int irr = 0;   /* types are run-time codes: every binder is relevant */
        ctx_bind(c, b->name, dv);
        Term *cod = check_type(c, s->a, &lb);
        ctx_pop(c);
        *ty = vu(la > lb ? la : lb);
        return mk_pi(b->name, dom, cod, irr);
    }
    case S_LAM: die("line %d: cannot infer the type of a lambda; add an annotation", s->line);
    case S_SYS: die("line %d: cannot infer the type of a system; it must be checked against a Partial type", s->line);
    case S_APP: case S_ELIM: case S_PATHP: case S_PARTIAL: case S_TRANSP: case S_HCOMP: case S_COMP: case S_SUB: case S_INS: case S_OUTS: return infer_app(c, s, ty);
    case S_LET: {
        int l; Term *tyt = check_type(c, s->a, &l);
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

static Term *check(Ctx *c, STerm *s, Val *ty) {
    if (s->k == S_LAM) {
        SBinder *b = &s->binders[0];
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
        return mk_lam(b->name, body, ty->irr);
    }
    if (s->k == S_LET) {
        int l; Term *tyt = check_type(c, s->a, &l);
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
    if (s->k == S_SYS) return check_system(c, s, ty);
    Val *got; Term *t = infer(c, s, &got);
    if (got->k == V_U && ty->k == V_U && got->n <= ty->n) return t;   /* cumulativity */
    if (got->k == V_PARTIAL && ty->k != V_PARTIAL && iv_is_one(got->a->iv)) got = got->b;   /* a partial element on a face that holds is an element */
    if (!conv(c->n, got, ty)) die("line %d: type mismatch: got %s, expected %s", s->line, show(c, got), show(c, ty));
    return t;
}

/* ---- declarations ---- */

static int mentions(Term *t, int d) {
    if (!t) return 0;
    switch (t->k) {
    case T_DATA: return t->n == d;
    case T_VAR: case T_U: case T_DEF: case T_CON: case T_ELIM: case T_INTERVAL: case T_I0: case T_I1: return 0;
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (mentions(t->br[i].face, d) || mentions(t->br[i].body, d)) return 1; return 0;
    default: return mentions(t->a, d) || mentions(t->b, d) || mentions(t->c, d) || mentions(t->d, d);
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
    for (int i = s->nparams - 1; i >= 0; i--) full = mk_pi(s->params[i].name, D.ptys[i], full, 0);
    { Term *x = ity; for (int j = 0; j < m; j++) { x->irr = 1; x = x->b; } }
    D.ty = full;
    int d = ndatas;
    datas = realloc(datas, (ndatas + 1) * sizeof(Data)); if (!datas) die("out of memory");
    datas[ndatas++] = D;
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
