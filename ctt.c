/*
 * ctt.c - eezott -C: the elaborated program printed as cubicaltt (M20, stage F4).
 *
 * The second oracle of the differential test is cubicaltt, the reference implementation of CCHM, independent of the
 * Agda lineage eezott followed for Glue. This file prints the checked program - the elaborated core - as one cubicaltt
 * module with its own small prelude:
 *   data types (parameters only: cubicaltt has no indexed families; eezott's Id, recognised by shape, is cubicaltt's
 *   builtin Id / idC / idJ; every other indexed family is UNSUPPORTED); path constructors with <i> systems;
 *   elim D -> a function elim_D defined by split, typed by eezott's own elim_type (cube methods as nested PathP);
 *   PathP, <i>, @; faces (i=0)(j=1) from the canonical DNF; hcomp A phi u u0 -> hComp A u0 [faces -> <j> t];
 *   transp L phi u0 -> comp (<i> L) u0 [faces -> <_> u0]; Glue with eezott's Equiv flipped into the kernel's shape
 *   (its fiber path runs the other way: PathP (<_> A) x (f y)); Sigma as (x : A) * B, pairs, .1 .2; U for every level;
 *   irrelevance dropped (cubicaltt has none: what eezott's .() lets pass, cubicaltt may refuse - a difference the other
 *   way, flagged by a comment line for the harness).
 * cubicaltt's lambdas carry their binder types, so every lambda is printed against an expected type: the definition's
 * telescope, the domain of the function it is passed to (the head's type instantiated along the spine, definitions
 * unfolded to a Pi when needed), a Sigma's component, a let's binding. A lambda in a position whose type the printer
 * cannot see is UNSUPPORTED.
 * What cubicaltt cannot say is reported, never approximated: a comment {- UNSUPPORTED: .. -} and exit status 3.
 *
 * Precedence follows Exp.cf: 0 Exp (lambda, let, <i>), 1 Exp1 (Pi, ->, Sigma), 2 Exp2 (application, @),
 * 3 Exp3 (PathP comp hComp Glue glue unglue Id idC idJ), 4 Exp4 (.1 .2), 5 atoms.
 */
#include "tt.h"
#include "machine.h"

static FILE *out;
static int nunsup, nirr, nhole;
static int id_data = -1;            /* the data type shaped like eezott's Id (params A, a; one index; refl): cubicaltt's builtin Id */
typedef struct { Term *ty; int depth, isi; } KTy;
/* the binders in scope, by level: grown (zero-filled) to any depth the printer reaches */
static KTy *ktys;
static const char **names;
static int kcap;
static void kgrow(int n) {   /* room for levels 0..n */
    if (n < kcap) return;
    int nc = kcap ? kcap : 64; while (nc <= n) nc *= 2;
    ktys = rrealloc(ktys, nc * sizeof(KTy)); names = rrealloc(names, nc * sizeof(char *));
    memset(ktys + kcap, 0, (nc - kcap) * sizeof(KTy)); memset(names + kcap, 0, (nc - kcap) * sizeof(char *));
    kcap = nc;
}
static char *needdef, *needdata;
static Term *I0, *I1;

static void unsupported(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    fputs("{- UNSUPPORTED: ", out); vfprintf(out, fmt, ap); fputs(" -}", out);
    va_end(ap); nunsup++;
}

/* ---------------- names ---------------- */

static const char *reserved[] = { "module", "where", "import", "data", "hdata", "split", "mutual", "opaque", "transparent",
    "transparent_all", "undefined", "let", "in", "U", "PathP", "comp", "hComp", "transport", "fill", "Glue", "glue", "unglue",
    "Id", "idC", "idJ", "with", "eqvFlip", "fibE", "fibC", "ctrT", "flipF", "flipB", "asc", NULL };
static int is_reserved(const char *s) { for (int i = 0; reserved[i]; i++) if (!strcmp(s, reserved[i])) return 1; return 0; }
static int is_global(const char *s) {
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, s)) return 1;
    for (int i = 0; i < ndatas; i++) if (!strcmp(datas[i].name, s)) return 1;
    for (int i = 0; i < ncons; i++) if (!strcmp(cons[i].name, s)) return 1;
    return 0;
}
/* cubicaltt identifiers: a letter then letters, digits, _ and '; a reserved word gets a prime; braces of an inserted implicit binder go */
static const char *mangle(const char *s) {
    size_t n = strlen(s); char *r = xalloc(n + 4); char *p = r;
    for (const char *q = s; *q; q++) if (*q != '{' && *q != '}') *p++ = *q;
    *p = 0;
    if (is_reserved(r)) { *p++ = '\''; *p = 0; }
    return r;
}
static const char *gname(TKind k, int id) {
    switch (k) {
    case T_DEF: return mangle(defs[id].name);
    case T_DATA: return mangle(datas[id].name);
    case T_CON: return mangle(cons[id].name);
    case T_ELIM: return xsprintf("elim_%s", mangle(datas[id].name));
    default: return "?";
    }
}
static const char *bind(int depth, const char *nm) {
    kgrow(depth);
    if (!nm || !strcmp(nm, "_")) nm = "x";
    const char *r = mangle(nm);
    for (;;) {
        int clash = is_global(r) || is_reserved(r);
        for (int i = 0; i < depth && !clash; i++) if (names[i] && !strcmp(names[i], r)) clash = 1;
        if (!clash) return r;
        r = xsprintf("%s'", r);
    }
}
static const char *vname(int depth, int idx) {
    kgrow(depth);
    int lvl = depth - 1 - idx;
    if (lvl >= 0 && lvl < depth && names[lvl]) return names[lvl];
    return xsprintf("#%d", idx);
}
static void binder_open(int depth, const char *nm, Term *ty) { kgrow(depth); names[depth] = bind(depth, nm); ktys[depth].ty = ty; ktys[depth].depth = depth; ktys[depth].isi = 0; }
static void ibinder_open(int depth, const char *nm) { kgrow(depth); names[depth] = bind(depth, nm && strcmp(nm, "_") ? nm : "i"); ktys[depth].ty = NULL; ktys[depth].depth = depth; ktys[depth].isi = 1; }
/* a binder is installed after its domain is printed: the domain's own binders live at the same level (agda.c learnt this) */
static void binder_set(int depth, const char *nm, Term *ty, int isi) { kgrow(depth); names[depth] = nm; ktys[depth].ty = ty; ktys[depth].depth = depth; ktys[depth].isi = isi; }

/* ---------------- faces ---------------- */

typedef struct { Term *t; int post; } FVItem;
static Stack fvist = { NULL, 0, 0, sizeof(FVItem) }, fvvst = { NULL, 0, 0, sizeof(IVal) };
static IVal face_iv(Term *t0, int depth) {
    size_t ib = fvist.n;
    FVItem it0 = { t0, 0 }; STACK_PUSH(&fvist, FVItem, it0);
    while (fvist.n > ib) {
        FVItem it = STACK_POP(&fvist, FVItem); Term *t = it.t;
        if (it.post) {
            if (t->k == T_INEG) { IVal a = STACK_POP(&fvvst, IVal); STACK_PUSH(&fvvst, IVal, iv_neg(a)); continue; }
            IVal b = STACK_POP(&fvvst, IVal), a = STACK_POP(&fvvst, IVal);
            STACK_PUSH(&fvvst, IVal, t->k == T_IAND ? iv_and(a, b) : iv_or(a, b));
            continue;
        }
        switch (t->k) {
        case T_I0: STACK_PUSH(&fvvst, IVal, iv_zero()); break;
        case T_I1: STACK_PUSH(&fvvst, IVal, iv_one()); break;
        case T_VAR: STACK_PUSH(&fvvst, IVal, iv_var(depth - 1 - t->n)); break;
        case T_IAND: case T_IOR: { FVItem p = { t, 1 }, b = { t->b, 0 }, a = { t->a, 0 }; STACK_PUSH(&fvist, FVItem, p); STACK_PUSH(&fvist, FVItem, b); STACK_PUSH(&fvist, FVItem, a); break; }
        case T_INEG: { FVItem p = { t, 1 }, a = { t->a, 0 }; STACK_PUSH(&fvist, FVItem, p); STACK_PUSH(&fvist, FVItem, a); break; }
        default: unsupported("face not an interval expression"); STACK_PUSH(&fvvst, IVal, iv_zero()); break;
        }
    }
    return STACK_POP(&fvvst, IVal);
}
static int conj_consistent(IConj *c) {
    for (int i = 0; i < c->n; i++) for (int j = i + 1; j < c->n; j++) if (c->l[i].var == c->l[j].var && c->l[i].neg != c->l[j].neg) return 0;
    return 1;
}
static void faces_print(IConj *c, int depth) {   /* (i=0) (j=1) .. */
    for (int l = 0; l < c->n; l++) fprintf(out, "%s(%s=%d)", l ? " " : "", vname(depth, depth - 1 - c->l[l].var), c->l[l].neg ? 0 : 1);
}

/* ---------------- types seen by the printer ---------------- */

static void tp(Term *t, int depth, int prec, Term *ty);
static void sys_sides(Term *sys, int depth, Term *elty);
static void tp_arg(Term *t, int depth, Term *ty) { tp(t, depth, 4, ty); }
static int spine(Term *t, Term ***argsp);
static Term *spine_head(Term *t);

static Term *global_ty(TKind k, int id) {
    Term *ty = k == T_DEF ? defs[id].ty : k == T_DATA ? datas[id].ty : k == T_CON ? cons[id].ty : NULL;
    if (!ty) return NULL;
    return ref_poly(k, id) ? subst_hidden(ty, lv_const(0)) : ty;
}
static Term *global_val(int id) { return defs[id].poly ? subst_hidden(defs[id].val, lv_const(0)) : defs[id].val; }
/* the type of a spine's head, in the current context: closed for globals, a binder's for variables */
static Term *head_type(Term *h, int depth) {
    kgrow(depth);
    switch (h->k) {
    case T_VAR: { int lvl = depth - 1 - h->n; if (lvl < 0 || lvl >= depth || !ktys[lvl].ty) return NULL; return shift(ktys[lvl].ty, 0, depth - ktys[lvl].depth); }
    case T_DEF: case T_DATA: case T_CON: return global_ty(h->k, h->n);
    case T_ELIM: return elim_type(h->n, lv_const(0), 0, lv_const(0));
    default: return NULL;
    }
}
/* a type as a Pi or a Sigma: itself when it is one; else with the definition at its head unfolded (as a term, so that nothing
   is elided or normalised), and failing that its value quoted back when that is one */
static Term *unfold_head(Term *t) {
    for (;;) {
        if (t->k == T_DEF) { t = global_val(t->n); continue; }
        if (t->k == T_LET) { t = inst_tele(t->c, 1, &t->b, 0); continue; }
        if (t->k != T_APP) return t;
        Term **args; int n = spine(t, &args);
        Term *h = spine_head(t), *hr = h->k == T_DEF ? global_val(h->n) : h->k == T_LAM ? h : NULL;
        if (!hr) return t;
        Term *v = hr; int i = 0;
        for (; i < n && v->k == T_LAM; i++) v = inst_tele(v->a, 1, &args[i], 0);
        for (; i < n; i++) v = mk_app(v, args[i], 0);
        if (v == t) return t;
        t = v;
    }
}
static Term *expose(Term *ty, int depth) {
    if (!ty || ty->k == T_PI || ty->k == T_SIGMA || ty->k == T_PATHP) return ty;
    { Term *u = unfold_head(ty); if (u->k == T_PI || u->k == T_SIGMA || u->k == T_PATHP) return u; }
    kgrow(depth); Env *e = NULL; for (int l = 0; l < depth; l++) e = env_push(e, ktys[l].isi ? vivar(l) : vvar(l));
    Val *v = force(eval(e, ty));
    if (v->k != V_PI && v->k != V_SIGMA && v->k != V_PATHP) return ty;
    return quote(depth, v);
}
static Term *pi_apply(Term *ty, Term *arg, int depth) {   /* the codomain of a Pi at an argument (NULL when ty is not one) */
    ty = expose(ty, depth);
    if (!ty || ty->k != T_PI) return NULL;
    return inst_tele(ty->b, 1, &arg, 0);
}
static Term *line_at(Term *line, Term *r) {   /* a line's body at an interval (NULL when it is not a lambda) */
    if (!line || line->k != T_LAM) return NULL;
    return inst_tele(line->a, 1, &r, 0);
}

/* the Id shape: data Id (A : U) (a : A) : A -> U with one nullary constructor at index a */
static int is_id_data(int d) {
    Data *D = &datas[d];
    if (D->nparams != 2 || D->nidx != 1 || D->ncons != 1 || D->nblock != 1) return 0;
    Con *C = &cons[D->cons[0]];
    if (C->nargs || C->nint) return 0;
    if (D->ptys[0]->k != T_U || D->ptys[1]->k != T_VAR || D->ptys[1]->n != 0) return 0;
    if (D->itys[0]->k != T_VAR || D->itys[0]->n != 1) return 0;
    return C->ridx[0]->k == T_VAR && C->ridx[0]->n == 0;
}

static int spine(Term *t, Term ***argsp) {   /* the arguments of an application, on the heap (any number) */
    int n = 0; Term *w = t;
    while (w->k == T_APP) { n++; w = w->a; }
    Term **args = xalloc((n + 1) * sizeof(Term *));
    w = t; for (int i = n - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    *argsp = args; return n;
}
static Term *spine_head(Term *t) { while (t->k == T_APP) t = t->a; return t; }

/* ---------------- terms ---------------- */

/* the body of a branch whose face is total (NULL: none): on a total face Glue A [-> (T, e)] is T, glue [-> t] a is t and
   unglue b is e.1 b - cubicaltt computes these but does not check or infer the forms themselves */
static Term *total_branch(Term *sys, int depth) {
    if (!sys || sys->k != T_SYS) return NULL;
    for (int i = 0; i < sys->nbr; i++) if (iv_is_one(face_iv(sys->br[i].face, depth))) return sys->br[i].body;
    return NULL;
}
/* eezott's e : Equiv T A (fiber f x = y) flipped into the kernel's shape (fiber x = f y): eqvFlip T A e */
/* a cube constructor's method as written, \is -> inS t: the element t under the same lambdas (its type is the nested PathP) */
static Term *strip_ins(Term *m) {
    int n = 0; Term *w = m;
    while (w->k == T_LAM) { n++; w = w->a; }
    if (w->k != T_INS) return NULL;
    Term **ls = xalloc((n + 1) * sizeof(Term *)); w = m;
    for (int i = 0; i < n; i++) { ls[i] = w; w = w->a; }
    Term *b = w->a;
    for (int i = n - 1; i >= 0; i--) { Term *r = mk_lam(ls[i]->name, b, ls[i]->irr); r->isi = ls[i]->isi; b = r; }
    return b;
}
static int is_cube_method_arg(Term *h, int i) {   /* argument i of an elim spine: the method of a cube constructor? */
    if (h->k != T_ELIM) return 0;
    Data *D = &datas[h->n]; int np = D->nparams, nbk = D->nblock, K = block_ncons(h->n);
    if (i < np + nbk || i >= np + nbk + K) return 0;
    int o = i - np - nbk;
    for (int k = 0; k < nbk; k++) { Data *M = &datas[D->block + k]; for (int ci = 0; ci < M->ncons; ci++) { Con *C = &cons[M->cons[ci]]; if (C->bord == o) return C->nint > 0 && !C->pathmethod && C->boundary; } }
    return 0;
}

/* ---------------- cubes: boundaries as nested PathP (as agda.c) ---------------- */

static Term *branch_at(TBranch *br, int nbr, int idx, int e, int depth) {
    IVal want = e ? iv_var(depth - 1 - idx) : iv_neg(iv_var(depth - 1 - idx));
    for (int i = 0; i < nbr; i++) if (iv_eq(face_iv(br[i].face, depth), want)) return br[i].body;
    return NULL;
}
static Term *cube(Term *ty, TBranch *br, int nbr, int n, int depth) {
    Term **b0 = xalloc((n + 1) * sizeof(Term *)), **b1 = xalloc((n + 1) * sizeof(Term *));
    for (int v = n - 1; v >= 0; v--) {
        b0[v] = branch_at(br, nbr, v, 0, depth); b1[v] = branch_at(br, nbr, v, 1, depth);
        if (!b0[v] || !b1[v]) return NULL;
    }
    Term *inner = ty;
    for (int m = 1; m <= n; m++) {
        int v = m - 1;
        Term *line = mk_lam("i", inner, 0); line->isi = 1;
        Term *e0 = subst_term(b0[v], v, I0), *e1 = subst_term(b1[v], v, I1);
        for (int q = m - 2; q >= 0; q--) { e0 = mk_lam("j", e0, 0); e0->isi = 1; e1 = mk_lam("j", e1, 0); e1->isi = 1; }
        inner = mk_term(T_PATHP, line, e0, e1, NULL);
    }
    return inner;
}
static Term *fix_method(Term *mt0, int depth0) {
    int k = 0; Term *mt = mt0;
    while (mt->k == T_PI && !(mt->isi || mt->a->k == T_INTERVAL)) { k++; mt = mt->b; }
    Term **ps = xalloc((k + 1) * sizeof(Term *)); { Term *w = mt0; for (int i = 0; i < k; i++) { ps[i] = w; w = w->b; } }
    int depth = depth0 + k;
    Term *r = mt;
    int n = 0; Term *w = mt;
    while (w->k == T_PI && (w->isi || w->a->k == T_INTERVAL)) { n++; w = w->b; }
    if (n == 0) r = mt;
    else if (w->k == T_SUB && w->c->k == T_SYS) { Term *c = cube(w->a, w->c->br, w->c->nbr, n, depth + n); if (c) r = c; else { unsupported("a cube method whose boundary is not a full cube"); r = mt; } }
    else if (w->k == T_PATHP) r = mt;
    else { unsupported("an interval-binder method without a boundary"); r = mt; }
    for (int i = k - 1; i >= 0; i--) { Term *p = mk_pi(ps[i]->name, ps[i]->a, r, ps[i]->irr); p->isi = ps[i]->isi; r = p; }
    return r;
}

/* ---------------- applications ---------------- */

/* a closed constructor spine of a Peano-shaped type, or a literal: suc^n zero (cubicaltt has no literals); -1: too large */
static long long unary_count(Term *t) {
    long long n = 0; int zi, si, d = -1;
    Term *w = t;
    while (w->k == T_APP && w->a->k == T_CON) { if (d < 0) { d = cons[w->a->n].data; if (!peano_shape(d, &zi, &si)) return 0; } if (w->a->n != si) return 0; n++; w = w->b; }
    if (w->k == T_NUM) { if (d < 0) { d = w->n; if (!peano_shape(d, &zi, &si)) return 0; } else if (w->n != d) return 0; char *s = bn_to_dec(w->num); if (strlen(s) > 4) { free(s); return -1; } n += strtoll(s, NULL, 10); free(s); }
    else if (w->k == T_CON) { if (d < 0) { d = cons[w->n].data; if (!peano_shape(d, &zi, &si)) return 0; } if (w->n != zi) return 0; }
    else return 0;
    return n > 4096 ? -1 : n;
}
static int peano_print(Term *t) {
    long long n = unary_count(t); int zi, si;
    if (n == 0 && !(t->k == T_CON && peano_shape(cons[t->n].data, &zi, &si) && t->n == zi) && !(t->k == T_NUM && peano_shape(t->n, &zi, &si))) return 0;
    if (n < 0) { unsupported("a numeral too large for unary"); return 1; }
    int d = t->k == T_NUM ? t->n : t->k == T_CON ? cons[t->n].data : cons[spine_head(t)->n].data;
    peano_shape(d, &zi, &si);
    for (long long q = 0; q < n; q++) fprintf(out, "(%s ", gname(T_CON, si));
    fputs(gname(T_CON, zi), out);
    for (long long q = 0; q < n; q++) fputc(')', out);
    return 1;
}

/* a pretype: a function over the interval, a partial element, a Sub type, a level, the sort Pre - nothing cubicaltt names.
   A definition of such a type (the prelude's hfill, say) has no cubicaltt image; its uses are unfolded at print, the
   arguments substituted (all definitions are non-recursive), so that only the primitives it abbreviates remain. */
static int pre_type_pre(Term *t, int d, void *ctx) {
    (void)d; (void)ctx;
    switch (t->k) {
    case T_PI: if (t->isi || t->pre || t->a->k == T_INTERVAL) return 1; term_any_push(t->b, 0); term_any_push(t->a, 0); return 2;
    case T_PARTIAL: case T_SUB: case T_INTERVAL: case T_LEVEL: return 1;
    case T_U: return t->pre ? 1 : -1;
    case T_SYS: return -1;
    default: return 0;
    }
}
static int pre_type(Term *t) { return term_any(t, 0, 1, pre_type_pre, NULL); }
static int inline_def(int id) { return pre_type(global_ty(T_DEF, id)); }

/* head reduction of what cubicaltt cannot name: a beta redex (comp's desugaring, an unfolded definition applied),
   outS (inS a), and a definition of a pretype at its use. The rest of the program is printed as written. */
typedef struct { Term *t; int k, n; Term **args; } RedItem;   /* a reduction waiting for its head's (k: T_OUTS, T_PAPP, T_APP) */
static Stack redst = { NULL, 0, 0, sizeof(RedItem) };
static Term *red(Term *t) {
    size_t base = redst.n;
    for (;;) {
        /* reduce t until it needs its head reduced first (a waiting item) or is done */
        Term *r;
        for (;;) {
            if (t->k == T_DEF && inline_def(t->n)) { t = global_val(t->n); continue; }
            if (t->k == T_OUTS) { RedItem it = { t, T_OUTS, 0, NULL }; STACK_PUSH(&redst, RedItem, it); t = t->d; continue; }
            if (t->k == T_PAPP) { RedItem it = { t, T_PAPP, 0, NULL }; STACK_PUSH(&redst, RedItem, it); t = t->a; continue; }
            if (t->k != T_APP) { r = t; break; }
            Term **args; int n = spine(t, &args);
            RedItem it = { t, T_APP, n, args }; STACK_PUSH(&redst, RedItem, it); t = spine_head(t);
        }
        /* r is a reduced head: the waiting reductions resume with it */
        for (;;) {
            if (redst.n == base) return r;
            RedItem it = STACK_POP(&redst, RedItem);
            if (it.k == T_OUTS) { if (r->k == T_INS) { t = r->a; break; } r = it.t; continue; }
            if (it.k == T_PAPP) { if (r->k == T_LAM && r->isi) { t = inst_tele(r->a, 1, &it.t->b, 0); break; } r = it.t; continue; }
            if (r->k != T_LAM) { r = it.t; continue; }
            Term *v = r; int i = 0;
            for (; i < it.n && v->k == T_LAM; i++) v = inst_tele(v->a, 1, &it.args[i], 0);
            for (; i < it.n; i++) v = mk_app(v, it.args[i], 0);
            t = v; break;
        }
    }
}


/* the sides of an hComp: every branch of sys (under [.., j], j the composition's direction named jn) whose face is conjoined
   with ctx; a branch whose body reduces to a system (a filler's partial element applied) contributes its own branches under
   the conjoined face */

/* ---- the printer on the machine (machine.h) ----
   tp and the printers it calls are frames: a term's printing, its binders' installation and every look at the binders in
   scope happen in the order the recursion took, with no C stack under them. A frame keeps what outlives a call in its
   fields; a flag shared down a system's nested branches lives on the heap. */
typedef struct {
    MHdr h;
    Term *t, *ty; int depth, prec;
    Term *a, *b, *ex, *hty, *hh, *elty, *T, *A, *e; Term **args;
    int n, i, c, d, d2, m, nint, neta, np, nargs, paren, first; int *firstp;
    const char *nm, *jn; IVal f, ctx;
} CttF;
#define F ((CttF *)(mst.p + off))
static void tp_step(size_t off);
static void app_step(size_t off);
static void lam_step(size_t off);
static void ilam_step(size_t off);
static void sys_sides_step(size_t off);
static void glue_sides_step(size_t off);
static void equiv_flip_step(size_t off);
static void hc_sides_step(size_t off);
static CttF *cpush(void (*step)(size_t), Term *t, int depth, int prec, Term *ty) { CttF *f = mpush(sizeof *f, step); f->t = t; f->depth = depth; f->prec = prec; f->ty = ty; return f; }
static void mpush_tp(Term *t, int depth, int prec, Term *ty) { cpush(tp_step, t, depth, prec, ty); }
static void mpush_sys_sides(Term *sys, int depth, Term *elty) { cpush(sys_sides_step, sys, depth, 0, elty); }
static void mpush_glue_sides(Term *Te, Term *A, int depth) { cpush(glue_sides_step, Te, depth, 0, NULL)->A = A; }
static void mpush_equiv_flip(Term *T, Term *A, Term *e, int depth) { CttF *f = cpush(equiv_flip_step, NULL, depth, 0, NULL); f->T = T; f->A = A; f->e = e; }
static void mpush_hc_sides(Term *sys, IVal ctx, int depth, const char *jn, Term *elty, int *first) {
    CttF *f = cpush(hc_sides_step, sys, depth, 0, elty); f->ctx = ctx; f->jn = jn; f->firstp = first;
}

/* consecutive interval lambdas: <i j> body; the body's type is the PathP's line under the binder */
static void ilam_step(size_t off) {
    MSTART
    if (F->prec > 0) fputc('(', out);
    fputc('<', out);
    {   int d = F->depth; Term *t = F->t, *ty = F->ty;
        while (t->k == T_LAM && t->isi) {
            ty = expose(ty, d);
            ty = ty && ty->k == T_PATHP && ty->a->k == T_LAM ? ty->a->a : NULL;   /* the line's body lives under the same binder */
            ibinder_open(d, t->name); fprintf(out, "%s%s", d > F->depth ? " " : "", names[d]); d++; t = t->a;
        }
        F->d = d; F->a = t; F->b = ty; }
    fputs("> ", out); MCALL(mpush_tp(F->a, F->d, 0, F->b));
    if (F->prec > 0) fputc(')', out);
    MRET(NULL);
    MFINISH
}
static void lam_step(size_t off) {
    MSTART
    if (F->prec > 0) fputc('(', out);
    fputs("\\", out); F->d = F->depth; F->a = F->t; F->b = F->ty;
    while (F->a->k == T_LAM && !F->a->isi) {
        { __typeof__(F->ex) st_ = expose(F->b, F->d); F->ex = st_; }
        if (!F->ex || F->ex->k != T_PI) { unsupported("a lambda whose type the printer cannot see"); const char *nm = bind(F->d, F->a->name); fprintf(out, " (%s : ?)", nm); binder_set(F->d, nm, NULL, 0); F->d++; F->a = F->a->a; F->b = NULL; continue; }
        if ((F->a->irr | F->ex->irr) & 2) nirr++;
        F->nm = bind(F->d, F->a->name);
        fprintf(out, " (%s : ", F->nm); MCALL(mpush_tp(F->ex->a, F->d, 0, NULL)); fputc(')', out);
        binder_set(F->d, F->nm, F->ex->a, 0);
        F->d++; F->a = F->a->a; F->b = F->ex->b;
    }
    fputs(" -> ", out); MCALL(mpush_tp(F->a, F->d, 0, F->b));
    if (F->prec > 0) fputc(')', out);
    MRET(NULL);
    MFINISH
}
/* [ faces -> e, .. ] */
static void sys_sides_step(size_t off) {
    MSTART
    fputc('[', out); F->first = 1;
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        F->f = face_iv(F->t->br[F->i].face, F->depth);
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            fputs(F->first ? " " : ", ", out); F->first = 0;
            faces_print(&F->f.c[F->c], F->depth); fputs(" -> ", out);
            MCALL(mpush_tp(F->t->br[F->i].body, F->depth, 0, F->ty));
        }
    }
    fputs(F->first ? "]" : " ]", out);
    MRET(NULL);
    MFINISH
}
/* eezott's e : Equiv T A (fiber f x = y) flipped into the kernel's shape (fiber x = f y): eqvFlip T A e */
static void equiv_flip_step(size_t off) {
    MSTART
    fputs("eqvFlip ", out); MCALL(mpush_tp(F->T, F->depth, 4, NULL)); fputc(' ', out);
    MCALL(mpush_tp(F->A, F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_tp(F->e, F->depth, 4, NULL));
    MRET(NULL);
    MFINISH
}
/* [ faces -> (T, eqvFlip T A e) ] */
static void glue_sides_step(size_t off) {
    MSTART
    if (F->t->k != T_SYS) { unsupported("a Glue system that is not written as a system"); MRET(NULL); }
    fputc('[', out); F->first = 1;
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        F->f = face_iv(F->t->br[F->i].face, F->depth);
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            fputs(F->first ? " " : ", ", out); F->first = 0;
            faces_print(&F->f.c[F->c], F->depth); fputs(" -> ", out);
            {   Term *b = F->t->br[F->i].body;
                F->T = b->k == T_PAIR ? b->a : mk_term(T_FST, b, NULL, NULL, NULL); F->e = b->k == T_PAIR ? b->b : mk_term(T_SND, b, NULL, NULL, NULL); }
            fputc('(', out); MCALL(mpush_tp(F->T, F->depth, 0, NULL)); fputs(", ", out);
            MCALL(mpush_equiv_flip(F->T, F->A, F->e, F->depth)); fputc(')', out);
        }
    }
    fputs(F->first ? "]" : " ]", out);
    MRET(NULL);
    MFINISH
}
/* the sides of an hComp: every branch of sys (under [.., j], j the composition's direction named jn) whose face is conjoined
   with ctx; a branch whose body reduces to a system (a filler's partial element applied) contributes its own branches under
   the conjoined face */
static void hc_sides_step(size_t off) {
    MSTART
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        F->f = iv_and(F->ctx, face_iv(F->t->br[F->i].face, F->depth));
        F->a = red(F->t->br[F->i].body);
        if (F->a->k == T_SYS) { MCALL(mpush_hc_sides(F->a, F->f, F->depth, F->jn, F->ty, F->firstp)); continue; }
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            {   int mentions_j = 0; for (int l = 0; l < F->f.c[F->c].n; l++) if (F->f.c[F->c].l[l].var == F->depth - 1) mentions_j = 1;
                if (mentions_j) { unsupported("a face mentioning the composition's own direction"); continue; } }
            fputs(*F->firstp ? " " : ", ", out); *F->firstp = 0;
            faces_print(&F->f.c[F->c], F->depth); fprintf(out, " -> <%s> ", F->jn);
            MCALL(mpush_tp(F->a, F->depth, 0, F->ty));
        }
    }
    MRET(NULL);
    MFINISH
}
static void app_step(size_t off) {
    MSTART
    F->n = spine(F->t, &F->args);
    F->hh = spine_head(F->t);
    /* the Id shape: the builtin */
    if (F->hh->k == T_DATA && F->hh->n == id_data && F->n == 3) {
        if (F->prec > 3) fputc('(', out);
        fputs("Id ", out); MCALL(mpush_tp(F->args[0], F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_tp(F->args[1], F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_tp(F->args[2], F->depth, 3, NULL));
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->hh->k == T_CON && cons[F->hh->n].data == id_data && F->n == 2) {
        if (F->prec > 3) fputc('(', out);
        fputs("idC (<_> ", out); MCALL(mpush_tp(F->args[1], F->depth, 0, NULL)); fputs(") [ -> ", out); MCALL(mpush_tp(F->args[1], F->depth, 0, NULL)); fputs(" ]", out);
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->hh->k == T_ELIM && F->hh->n == id_data) {
        if (F->n < 6) { unsupported("elim Id not fully applied"); MRET(NULL); }
        if (F->prec > 2 || (F->prec > 3 && F->n == 6)) fputc('(', out);
        if (F->n > 6) fputc('(', out);
        fputs("idJ", out);
        { __typeof__(F->hty) st_ = head_type(F->hh, F->depth); F->hty = st_; }
        for (F->i = 0; F->i < F->n; F->i++) {
            fputc(' ', out);
            MCALL(mpush_tp(F->args[F->i], F->depth, 4, F->hty && F->hty->k == T_PI ? F->hty->a : NULL));
            { __typeof__(F->hty) st_ = pi_apply(F->hty, F->args[F->i], F->depth); F->hty = st_; }
            if (F->i == 5 && F->n > 6) fputc(')', out);
        }
        if (F->prec > 2 || (F->prec > 3 && F->n == 6)) fputc(')', out);
        MRET(NULL);
    }
    /* a path constructor's missing intervals; a constructor's missing arguments (eta-expanded: cubicaltt checks a constructor
       against its data type only) */
    F->nint = 0; F->neta = 0; F->np = 0; F->nargs = 0;
    if (F->hh->k == T_CON) { Con *C = &cons[F->hh->n]; F->np = datas[C->data].nparams; F->nargs = C->nargs; if (C->nint && F->n < F->np + F->nargs + C->nint) F->nint = F->np + F->nargs + C->nint - F->n; if (!C->nint && F->n < F->np + F->nargs) F->neta = F->np + F->nargs - F->n; }
    if (F->nint && F->n < F->np + F->nargs) { unsupported("a path constructor partially applied before its interval arguments"); F->nint = 0; }
    F->m = F->nint + F->neta; F->d2 = F->depth + F->m;
    F->paren = F->m ? F->prec > 0 : (F->prec > 2 && F->n > 0);
    if (F->paren) fputc('(', out);
    if (F->nint) { fputc('<', out); for (int q = 0; q < F->nint; q++) { ibinder_open(F->depth + q, xsprintf("i%d", q)); fprintf(out, "%s%s", q ? " " : "", names[F->depth + q]); } fputs("> ", out); }
    if (F->neta) {   /* \ (a : A) .. -> c args.. a ..: the binder types from the head's type at the given arguments */
        { __typeof__(F->b) st_ = head_type(F->hh, F->depth); F->b = st_; }
        for (int i = 0; i < F->n; i++) { __typeof__(F->b) st_ = pi_apply(F->b, F->args[i], F->depth); F->b = st_; }
        fputs("\\", out);
        for (F->c = 0; F->c < F->neta; F->c++) {
            { __typeof__(F->ex) st_ = expose(F->b, F->depth + F->c); F->ex = st_; }
            if (!F->ex || F->ex->k != T_PI) { unsupported("the type of a constructor's missing argument"); break; }
            F->nm = bind(F->depth + F->c, F->ex->name);
            fprintf(out, " (%s : ", F->nm); MCALL(mpush_tp(F->ex->a, F->depth + F->c, 0, NULL)); fputc(')', out);
            binder_set(F->depth + F->c, F->nm, F->ex->a, 0); F->b = F->ex->b;
        }
        fputs(" -> ", out);
    }
    if (F->m) { F->t = shift(F->t, 0, F->m); F->n = spine(F->t, &F->args); F->hh = spine_head(F->t); }   /* the given arguments, under the new binders */
    { __typeof__(F->hty) st_ = head_type(F->hh, F->d2); F->hty = st_; }
    if (F->hh->k == T_CON) {
        Con *C = &cons[F->hh->n];
        if (C->nint) {   /* a path constructor: c{D p..} a.. @ i.. */
            fprintf(out, "%s{%s", gname(T_CON, F->hh->n), gname(T_DATA, C->data));
            for (F->i = 0; F->i < F->np && F->i < F->n; F->i++) { fputc(' ', out); MCALL(mpush_tp(F->args[F->i], F->d2, 4, NULL)); }
            fputc('}', out);
        } else fputs(gname(T_CON, F->hh->n), out);
    } else if (F->hh->k == T_DEF || F->hh->k == T_DATA || F->hh->k == T_ELIM) fputs(gname(F->hh->k, F->hh->n), out);
    else MCALL(mpush_tp(F->hh, F->d2, 2, NULL));
    for (F->i = 0; F->i < F->n; F->i++) {
        {   Term *ex = expose(F->hty, F->d2);
            F->a = ex && ex->k == T_PI ? ex->a : NULL;   /* the domain */
            F->c = ex && ex->k == T_PI && (ex->isi || ex->a->k == T_INTERVAL);
            if (ex && ex->k == T_PI && (ex->irr & 2)) nirr++; }
        if (F->hh->k == T_CON && (F->i < F->np)) { { __typeof__(F->hty) st_ = pi_apply(F->hty, F->args[F->i], F->d2); F->hty = st_; } continue; }   /* a constructor's parameters: cubicaltt infers them (or they went into the braces) */
        if (F->c) { fputs(" @ ", out); MCALL(mpush_tp(F->args[F->i], F->d2, 5, NULL)); }
        else if (is_cube_method_arg(F->hh, F->i)) {   /* typed by the method's nested-PathP form: its element binders, then the interval lambdas along the PathP lines */
            F->b = strip_ins(F->args[F->i]); fputc(' ', out);
            if (F->b) MCALL(mpush_tp(F->b, F->d2, 4, F->a ? fix_method(F->a, F->d2) : NULL));
            else { unsupported("a cube method not of the form \\is -> inS t"); MCALL(mpush_tp(F->args[F->i], F->d2, 4, NULL)); }
        }
        else { fputc(' ', out); MCALL(mpush_tp(F->args[F->i], F->d2, 4, F->a)); }
        { __typeof__(F->hty) st_ = pi_apply(F->hty, F->args[F->i], F->d2); F->hty = st_; }
    }
    for (int q = 0; q < F->neta; q++) fprintf(out, " %s", names[F->depth + q]);
    for (int q = 0; q < F->nint; q++) fprintf(out, " @ %s", names[F->depth + q]);
    if (F->paren) fputc(')', out);
    MRET(NULL);
    MFINISH
}
static void tp_step(size_t off) {
    MSTART
    if (!F->t) { fputs("?", out); MRET(NULL); }
    F->t = red(F->t);
    if ((F->t->k == T_APP || F->t->k == T_CON || F->t->k == T_NUM) && peano_print(F->t)) MRET(NULL);
    switch (F->t->k) {   /* the kinds that print nothing below them (no resume point inside this switch) */
    case T_VAR: fputs(vname(F->depth, F->t->n), out); MRET(NULL);
    case T_U: if (F->t->pre) unsupported("the sort of pretypes"); else fputs("U", out); MRET(NULL);
    case T_LEVEL: case T_LZERO: case T_LSUC: case T_LMAX: case T_LVAL: case T_LMETA: unsupported("a universe level"); MRET(NULL);
    case T_META: unsupported("unsolved meta"); MRET(NULL);
    case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_APP: MBECOME(app_step);
    case T_NUM: unsupported("a literal of a type not shaped like the naturals"); MRET(NULL);
    case T_IRR: fputc('?', out); nhole++; MRET(NULL);   /* an elided irrelevant value (a word's proof component): a hole, which cubicaltt checks trivially, as eezott never compares it */
    case T_INTERVAL: unsupported("the interval as a type"); MRET(NULL);
    case T_I0: fputs("0", out); MRET(NULL);
    case T_I1: fputs("1", out); MRET(NULL);
    case T_LAM: if (F->t->isi) MBECOME(ilam_step); MBECOME(lam_step);
    case T_PARTIAL: case T_SYS: case T_SUB: case T_INS: unsupported("a partial element, a Sub type or inS outside hcomp/Glue/a cube method"); MRET(NULL);
    case T_INEG: case T_IAND: case T_IOR: case T_PI: case T_SIGMA: case T_PAIR: case T_FST: case T_SND: case T_LET: case T_PATHP: case T_PAPP:
    case T_OUTS: case T_TRANSP: case T_HCOMP: case T_GLUE: case T_GLUEEL: case T_UNGLUE: break;
    default: MRET(NULL);
    }
    if (F->t->k == T_INEG) {   /* never --: a line comment */
        fputc('-', out);
        if (F->t->a->k == T_INEG) { fputc('(', out); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL)); fputc(')', out); } else MCALL(mpush_tp(F->t->a, F->depth, 5, NULL));
        MRET(NULL);
    }
    if (F->t->k == T_IAND || F->t->k == T_IOR) {
        fputc('(', out); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL)); fputs(F->t->k == T_IAND ? " /\\ " : " \\/ ", out); MCALL(mpush_tp(F->t->b, F->depth, 0, NULL)); fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PI) {
        if (F->t->isi || F->t->a->k == T_INTERVAL) { unsupported("a function over the interval"); MRET(NULL); }
        if (F->t->irr & 2) nirr++;
        if (F->prec > 1) fputc('(', out);
        F->c = term_mentions_var(F->t->b, 0);
        if (!F->c) { MCALL(mpush_tp(F->t->a, F->depth, 2, NULL)); fputs(" -> ", out); binder_open(F->depth, "_", F->t->a); }
        else { F->nm = bind(F->depth, F->t->name); fprintf(out, "(%s : ", F->nm); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL)); fputs(") -> ", out); binder_set(F->depth, F->nm, F->t->a, 0); }
        MCALL(mpush_tp(F->t->b, F->depth + 1, 1, NULL));
        if (F->prec > 1) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_SIGMA) {
        if (F->t->irr) nirr++;
        if (F->prec > 1) fputc('(', out);
        F->nm = bind(F->depth, F->t->name); fprintf(out, "(%s : ", F->nm); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL)); fputs(") * ", out); binder_set(F->depth, F->nm, F->t->a, 0);
        MCALL(mpush_tp(F->t->b, F->depth + 1, 1, NULL));
        if (F->prec > 1) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PAIR) {
        {   Term *ex = expose(F->ty, F->depth);
            F->a = ex && ex->k == T_SIGMA ? ex->a : NULL; F->b = ex && ex->k == T_SIGMA ? inst_tele(ex->b, 1, &F->t->a, 0) : NULL; }
        if (F->t->irr) nirr++;
        fputc('(', out); MCALL(mpush_tp(F->t->a, F->depth, 0, F->a)); fputs(", ", out); MCALL(mpush_tp(F->t->b, F->depth, 0, F->b)); fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_FST || F->t->k == T_SND) {
        if (F->prec > 4) fputc('(', out);
        MCALL(mpush_tp(F->t->a, F->depth, 4, NULL)); fputs(F->t->k == T_FST ? ".1" : ".2", out);
        if (F->prec > 4) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_LET) {
        if (pre_type(F->t->a)) { Term *u = inst_tele(F->t->c, 1, &F->t->b, 0); int d = F->depth, p = F->prec; Term *ty = F->ty; MTAIL(mpush_tp(u, d, p, ty)); }   /* a let of a pretype (lemIso's fillers): unfolded at its uses */
        if (F->prec > 0) fputc('(', out);
        if (F->t->irr & 2) nirr++;
        /* layout, not braces: the stop word 'in' would close the module's implicit block past an explicit one (BNFC's resolver) */
        F->nm = bind(F->depth, F->t->name); fprintf(out, "let %s : ", F->nm); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL));
        fputs(" = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0, F->t->a)); fputs(" in ", out); binder_set(F->depth, F->nm, F->t->a, 0);
        MCALL(mpush_tp(F->t->c, F->depth + 1, 0, F->ty ? shift(F->ty, 0, 1) : NULL));
        if (F->prec > 0) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PATHP) {
        if (F->prec > 3) fputc('(', out);
        fputs("PathP ", out); MCALL(mpush_tp(F->t->a, F->depth, 4, NULL)); fputc(' ', out);
        MCALL(mpush_tp(F->t->b, F->depth, 4, line_at(F->t->a, I0))); fputc(' ', out); MCALL(mpush_tp(F->t->c, F->depth, 4, line_at(F->t->a, I1)));
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PAPP) {
        if (F->prec > 2) fputc('(', out);
        MCALL(mpush_tp(F->t->a, F->depth, 2, NULL)); fputs(" @ ", out); MCALL(mpush_tp(F->t->b, F->depth, 5, NULL));
        if (F->prec > 2) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_OUTS) {
        {   Term *h = F->t->d; while (h->k == T_APP || h->k == T_PAPP) h = h->a;
            if (h->k == T_VAR) { int lvl = F->depth - 1 - h->n; kgrow(F->depth); Term *kt = (lvl >= 0 && lvl < F->depth) ? ktys[lvl].ty : NULL;
                if (kt && kt->k == T_PATHP) { Term *u = F->t->d; int d = F->depth, p = F->prec; Term *ty = F->ty; MTAIL(mpush_tp(u, d, p, ty)); } } }   /* the element of a cube method: the method is the path itself */
        unsupported("outS"); MRET(NULL);
    }
    if (F->t->k == T_TRANSP) {   /* comp (<i> L) u0 [ faces(phi) -> <_> u0 ] */
        if (F->prec > 3) fputc('(', out);
        fputs("comp ", out); MCALL(mpush_tp(F->t->a, F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_tp(F->t->c, F->depth, 4, line_at(F->t->a, I0))); fputc(' ', out);
        F->f = face_iv(F->t->b, F->depth); fputc('[', out); F->first = 1;
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            fputs(F->first ? " " : ", ", out); F->first = 0; faces_print(&F->f.c[F->c], F->depth); fputs(" -> <_> ", out);
            MCALL(mpush_tp(F->t->c, F->depth, 0, NULL));
        }
        fputs(F->first ? "]" : " ]", out);
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_HCOMP) {   /* comp (<_> A) u0 [ faces -> <j> t ]: hcomp is composition along the constant line (CCHM); cubicaltt's own
                                   hComp is a stuck value on every type, its comp computes on data, in U and along the lines composed there */
        F->b = red(F->t->c);
        F->e = F->b->k == T_LAM && F->b->isi ? red(F->b->a) : NULL;
        if (!F->e || F->e->k != T_SYS) { unsupported("an hcomp whose system is not written as one"); MRET(NULL); }
        if (F->prec > 3) fputc('(', out);
        fputs("comp (<_> ", out); MCALL(mpush_tp(F->t->a, F->depth, 0, NULL)); fputs(") ", out); MCALL(mpush_tp(F->t->d, F->depth, 4, F->t->a)); fputc(' ', out);
        ibinder_open(F->depth, F->b->name);
        fputc('[', out); F->firstp = xalloc(sizeof(int)); *F->firstp = 1;
        MCALL(mpush_hc_sides(F->e, iv_one(), F->depth + 1, names[F->depth], shift(F->t->a, 0, 1), F->firstp));
        fputs(*F->firstp ? "]" : " ]", out);
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_GLUE) {
        {   Term *tot = total_branch(F->t->c, F->depth);
            if (tot) { Term *u = tot->k == T_PAIR ? tot->a : mk_term(T_FST, tot, NULL, NULL, NULL); int d = F->depth, p = F->prec; Term *ty = F->ty; MTAIL(mpush_tp(u, d, p, ty)); } }
        if (F->prec > 3) fputc('(', out);
        fputs("Glue ", out); MCALL(mpush_tp(F->t->a, F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_glue_sides(F->t->c, F->t->a, F->depth));
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_GLUEEL) {
        {   Term *tot = total_branch(F->t->a, F->depth);
            if (tot) { int d = F->depth, p = F->prec; Term *ty = F->ty; MTAIL(mpush_tp(tot, d, p, ty)); } }
        if (F->prec > 3) fputc('(', out);
        fputs("glue ", out); MCALL(mpush_tp(F->t->b, F->depth, 4, F->t->c && F->t->c->k == T_GLUE ? F->t->c->a : NULL)); fputc(' ', out);
        if (F->t->a->k == T_SYS) MCALL(mpush_sys_sides(F->t->a, F->depth, NULL)); else unsupported("a glue system that is not written as one");
        if (F->prec > 3) fputc(')', out);
        MRET(NULL);
    }
    /* T_UNGLUE */
    {   Term *tot = total_branch(F->t->d, F->depth);
        if (tot) { Term *e = tot->k == T_PAIR ? tot->b : mk_term(T_SND, tot, NULL, NULL, NULL); Term *u = mk_app(mk_term(T_FST, e, NULL, NULL, NULL), F->t->a, 0); int d = F->depth, p = F->prec; Term *ty = F->ty; MTAIL(mpush_tp(u, d, p, ty)); } }
    if (F->prec > 3) fputc('(', out);
    F->b = red(F->t->a);
    fputs("unglue ", out);
    if (F->b->k == T_GLUEEL || F->b->k == T_PAIR || F->b->k == T_LAM || F->b->k == T_CON) {   /* cubicaltt infers unglue's argument: what it only checks is ascribed its Glue type */
        fputs("(asc ", out); MCALL(mpush_tp(mk_term(T_GLUE, F->t->b, F->t->c, F->t->d, NULL), F->depth, 4, NULL)); fputc(' ', out); MCALL(mpush_tp(F->b, F->depth, 4, NULL)); fputc(')', out);
    } else MCALL(mpush_tp(F->b, F->depth, 4, NULL));
    fputc(' ', out); MCALL(mpush_glue_sides(F->t->d, F->t->b, F->depth));
    if (F->prec > 3) fputc(')', out);
    MRET(NULL);
    MFINISH
}
#undef F
/* the C entries (the declarations' printers call these; each runs the machine to the end of its term) */
static void tp(Term *t, int depth, int prec, Term *ty) { mpush_tp(t, depth, prec, ty); mrun(); }
static void sys_sides(Term *sys, int depth, Term *elty) { mpush_sys_sides(sys, depth, elty); mrun(); }

/* ---------------- declarations ---------------- */

static void print_def(int i) {
    fprintf(out, "%s", gname(T_DEF, i));
    Term *ty = global_ty(T_DEF, i), *v = global_val(i); int depth = 0;
    for (;;) {
        Term *ex = expose(ty, depth);
        if (!(v->k == T_LAM && !v->isi && ex && ex->k == T_PI && !(ex->isi || ex->a->k == T_INTERVAL))) break;
        if ((ex->irr | v->irr) & 2) nirr++;
        const char *nm = bind(depth, v->name);
        fprintf(out, " (%s : ", nm); tp(ex->a, depth, 0, NULL); fputc(')', out);
        binder_set(depth, nm, ex->a, 0);
        depth++; v = v->a; ty = ex->b;
    }
    fputs(" : ", out); tp(ty, depth, 0, NULL); fputs(" = ", out); tp(v, depth, 0, ty); fputs("\n\n", out);
}

static void data_decl(int d) {
    Data *D = &datas[d];
    if (D->nidx) { unsupported("data %s: an indexed family (cubicaltt has parameters only)", D->name); fputs("\n\n", out); return; }
    int depth = 0;
    fprintf(out, "data %s", gname(T_DATA, d));
    for (int i = 0; i < D->nparams; i++) { const char *nm = bind(depth, xsprintf("p%d", i)); fprintf(out, " (%s : ", nm); tp(D->ptys[i], depth, 0, NULL); fputc(')', out); binder_set(depth, nm, D->ptys[i], 0); depth++; }
    fputs(" =", out);
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fprintf(out, "%s %s", ci ? "\n  |" : "", gname(T_CON, D->cons[ci]));
        int dep = depth;
        for (int j = 0; j < C->nargs; j++) { ConArg *A = &C->args[j]; if (A->irr & 2) nirr++; const char *nm = bind(dep, A->name); fprintf(out, " (%s : ", nm); tp(A->ty, dep, 0, NULL); fputc(')', out); binder_set(dep, nm, A->ty, 0); dep++; }
        if (C->nint) {
            if (!C->boundary) { unsupported("constructor %s has interval binders but no boundary", C->name); continue; }
            fputs(" <", out);
            for (int q = 0; q < C->nint; q++) { ibinder_open(dep + q, xsprintf("i%d", q)); fprintf(out, "%s%s", q ? " " : "", names[dep + q]); }
            fputs("> ", out);
            sys_sides(C->boundary, dep + C->nint, NULL);
        }
    }
    fputs("\n\n", out);
}

/* the eliminator as a split: elim_D (p..) (P..) (m..) : (x : D p) -> P x = split { c a.. -> m a.. ih.. ; loop a.. @ i -> m a.. ih.. @ i } */
static void print_elim(int d) {
    Data *D = &datas[d];
    if (D->nidx) return;   /* an indexed family has no cubicaltt image (Id is the builtin) */
    int np = D->nparams, nbk = D->nblock, K = block_ncons(d);
    for (int k = 0; k < nbk; k++) if (datas[D->block + k].nidx) { unsupported("elim of a block with an indexed member"); fputs("\n\n", out); return; }
    const char *en = gname(T_ELIM, d);
    Term *ety = elim_type(d, lv_const(0), 0, lv_const(0));
    int depth = 0;
    fprintf(out, "%s", en);
    /* the telescope: params, motives, methods; the last binder x stays in the type */
    Term *w = ety; int nb = 0, total = np + nbk + K;
    const char **bn = xalloc((total + 2) * sizeof(char *));
    while (w->k == T_PI && nb < total) {
        Term *dom = w->a;
        if (w->name && !strncmp(w->name, "m_", 2)) dom = fix_method(dom, depth);
        if (w->irr & 2) nirr++;
        const char *nm = bind(depth, w->name); bn[nb] = nm;
        fprintf(out, " (%s : ", nm); tp(dom, depth, 0, NULL); fputc(')', out);
        binder_set(depth, nm, dom, 0);
        depth++; nb++; w = w->b;
    }
    fputs(" : ", out); tp(w, depth, 0, NULL); fputs(" = split {", out);
    const char **pn = bn, **Pn = bn + np, **mn = bn + np + nbk;
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]]; int r = C->nargs;
        fprintf(out, "%s %s", ci ? ";" : "", gname(T_CON, D->cons[ci]));
        const char **an = xalloc((r + 1) * sizeof(char *)); int dep = depth;
        for (int j = 0; j < r; j++) { binder_open(dep, C->args[j].name && strcmp(C->args[j].name, "_") ? C->args[j].name : xsprintf("a%d", j), NULL); an[j] = names[dep]; fprintf(out, " %s", an[j]); dep++; }
        const char **in = xalloc((C->nint + 1) * sizeof(char *));
        if (C->nint) { fputs(" @", out); for (int q = 0; q < C->nint; q++) { ibinder_open(dep + q, xsprintf("j%d", q)); in[q] = names[dep + q]; fprintf(out, " %s", in[q]); } }
        fprintf(out, " -> %s", mn[C->bord]);
        for (int j = 0; j < r; j++) fprintf(out, " %s", an[j]);
        /* induction hypotheses, in argument order */
        for (int j = 0; j < r; j++) {
            ConArg *A = &C->args[j];
            if (!A->isrec && !A->isrecpath) continue;
            int rm = A->rec;
            int q = A->isrecpath ? 1 : A->npi;
            int ydep = depth + j;   /* the y binders live above [params, a_0..a_{j-1}]: opened at the levels of a_j.., restored after */
            fputs(" (", out);
            if (A->isrecpath) { ibinder_open(ydep, "k"); fprintf(out, "<%s> ", names[ydep]); }
            else if (q) {
                /* the argument's type under [params, a_0..a_{j-1}]: its Pi binders are the hypothesis's lambdas; the params sit
                   at levels 0.., the a's at depth.., so indices >= j (the params) move up by the motive and method binders */
                Term *w2 = shift(A->ty, j, nbk + K);
                fputs("\\", out);
                for (int y = 0; y < q && w2->k == T_PI; y++) { const char *nm = bind(ydep + y, xsprintf("y%d", y)); fprintf(out, " (%s : ", nm); tp(w2->a, ydep + y, 0, NULL); fputc(')', out); binder_set(ydep + y, nm, w2->a, 0); w2 = w2->b; }
                fputs(" -> ", out);
            }
            fputs(gname(T_ELIM, rm), out);
            for (int i = 0; i < np; i++) fprintf(out, " %s", pn[i]);
            for (int i = 0; i < nbk; i++) fprintf(out, " %s", Pn[i]);
            for (int i = 0; i < K; i++) fprintf(out, " %s", mn[i]);
            if (A->isrecpath) fprintf(out, " (%s @ %s))", an[j], names[ydep]);
            else if (q) { fprintf(out, " (%s", an[j]); for (int y = 0; y < q; y++) fprintf(out, " %s", names[ydep + y]); fputs("))", out); }
            else fprintf(out, " %s)", an[j]);
            /* restore the argument names shadowed by the y binders */
            for (int y = 0; y < q && j + y < r; y++) { names[depth + j + y] = an[j + y]; ktys[depth + j + y].ty = NULL; ktys[depth + j + y].isi = 0; }
            for (int y = 0; y < q; y++) if (j + y >= r && j + y < r + C->nint) { names[depth + j + y] = in[j + y - r]; ktys[depth + j + y].ty = NULL; ktys[depth + j + y].isi = 1; }
        }
        for (int q = 0; q < C->nint; q++) fprintf(out, " @ %s", in[q]);
    }
    fputs(" }\n\n", out);
}

static void header(const char *modname) {
    fprintf(out, "module %s where\n", modname);
    fputs("-- generated by eezott -C: the elaborated program, for cubicaltt as the differential oracle (M20 F4)\n", out);
    /* eezott's Equiv T A = (f : T -> A) * ((y : A) -> isContr ((x : T) * Path A (f x) y)); the kernel's Glue wants the fiber's path the
       other way round: (x : T) * PathP (<_> A) y (f x). eqvFlip reverses the paths, componentwise. */
    fputs("fibE (T A : U) (f : T -> A) (y : A) : U = (x : T) * PathP (<_> A) (f x) y\n", out);
    fputs("fibC (T A : U) (f : T -> A) (y : A) : U = (x : T) * PathP (<_> A) y (f x)\n", out);
    fputs("ctrT (X : U) : U = (s : X) * ((z : X) -> PathP (<_> X) s z)\n", out);
    fputs("asc (A : U) (x : A) : A = x\n", out);
    fputs("flipF (T A : U) (f : T -> A) (y : A) (u : fibE T A f y) : fibC T A f y = (u.1, <i> u.2 @ -i)\n", out);
    fputs("flipB (T A : U) (f : T -> A) (y : A) (u : fibC T A f y) : fibE T A f y = (u.1, <i> u.2 @ -i)\n", out);
    fputs("eqvFlip (T A : U) (e : (f : T -> A) * ((y : A) -> ctrT (fibE T A f y))) : (f : T -> A) * ((y : A) -> ctrT (fibC T A f y)) =\n"
          "  (e.1, \\ (y : A) -> (flipF T A e.1 y (e.2 y).1,\n"
          "                     \\ (z : fibC T A e.1 y) -> <i> flipF T A e.1 y ((e.2 y).2 (flipB T A e.1 y z) @ i)))\n\n", out);
}

typedef struct { int seq, isdata, id; } Decl;
static int decl_cmp(const void *a, const void *b) { return ((const Decl *)a)->seq - ((const Decl *)b)->seq; }
/* what the module needs: definitions and data types reached from the program's own, marked on a work list */
static Stack needst = { NULL, 0, 0, sizeof(Term *) };
static void need_push(Term *t) { if (t) STACK_PUSH(&needst, Term *, t); }
static void need_data_mark(int d) {
    Data *D = &datas[d]; if (needdata[d]) return;
    for (int k = 0; k < D->nblock; k++) {
        int m = D->block + k; if (needdata[m]) continue; needdata[m] = 1;
        Data *M = &datas[m];
        for (int i = 0; i < M->nparams; i++) need_push(M->ptys[i]);
        for (int j = 0; j < M->nidx; j++) need_push(M->itys[j]);
        for (int ci = 0; ci < M->ncons; ci++) { Con *C = &cons[M->cons[ci]]; for (int j = 0; j < C->nargs; j++) need_push(C->args[j].ty); for (int j = 0; j < M->nidx; j++) need_push(C->ridx[j]); if (C->boundary) need_push(C->boundary); }
    }
}
static void need_def_mark(int i) { if (needdef[i]) return; needdef[i] = 1; need_push(defs[i].ty); need_push(defs[i].val); }
static void need_run(void) {
    while (needst.n) {
        Term *t = STACK_POP(&needst, Term *);
        switch (t->k) {
        case T_DEF: need_def_mark(t->n); break;
        case T_DATA: case T_ELIM: need_data_mark(t->n); break;
        case T_CON: need_data_mark(cons[t->n].data); break;
        case T_NUM: need_data_mark(t->n); break;
        case T_SYS: for (int i = 0; i < t->nbr; i++) { need_push(t->br[i].face); need_push(t->br[i].body); } break;
        default: need_push(t->a); need_push(t->b); need_push(t->c); need_push(t->d); break;
        }
    }
}
static void need_def(int i) { need_def_mark(i); need_run(); }
static void need_data(int d) { need_data_mark(d); need_run(); }
static int irr_value_pre(Term *t, int d, void *ctx) { (void)d; (void)ctx; return t->k == T_IRR; }
static int has_irr_value(Term *t) { return term_any(t, 0, 1, irr_value_pre, NULL); }

int ctt_program(FILE *f, const char *modname, int first_seq, const char *nfname) {
    out = f; nunsup = 0; nirr = 0; nhole = 0;
    I0 = mk_term(T_I0, NULL, NULL, NULL, NULL); I1 = mk_term(T_I1, NULL, NULL, NULL, NULL);
    for (int d = 0; d < ndatas; d++) if (id_data < 0 && is_id_data(d)) id_data = d;
    needdef = xalloc(ndefs + 1); needdata = xalloc(ndatas + 1);
    for (int i = 0; i < ndefs; i++) if (defs[i].seq >= first_seq) need_def(i);
    for (int d = 0; d < ndatas; d++) if (datas[d].seq >= first_seq) need_data(d);
    header(modname);
    Decl *ds = xalloc((ndefs + ndatas + 1) * sizeof(Decl)); int nd = 0;
    for (int i = 0; i < ndefs; i++) if (needdef[i]) ds[nd++] = (Decl){ defs[i].seq, 0, i };
    for (int d = 0; d < ndatas; d++) if (needdata[d] && datas[d].bpos == 0) ds[nd++] = (Decl){ datas[d].seq, 1, d };
    qsort(ds, nd, sizeof(Decl), decl_cmp);
    for (int i = 0; i < nd; i++) {
        if (!ds[i].isdata) { if (inline_def(ds[i].id)) fprintf(out, "-- %s: a definition of a pretype, unfolded at its uses\n\n", gname(T_DEF, ds[i].id)); else print_def(ds[i].id); continue; }
        int d = ds[i].id; Data *D = &datas[d];
        if (d == id_data) { fputs("-- Id: cubicaltt's builtin (Id, idC, idJ)\n\n", out); continue; }
        if (D->nblock == 1) { data_decl(d); print_elim(d); }
        else {   /* two mutual blocks: cubicaltt's resolver gives the types of a block's members the block's names but not its
                    constructors (Resolver.hs resolveDecl: only the bodies see ns), and the eliminators' types mention them */
            fputs("mutual {\n", out);
            for (int k = 0; k < D->nblock; k++) { fputs(k ? ";\n" : "", out); data_decl(D->block + k); }
            fputs("}\n\nmutual {\n", out);
            for (int k = 0; k < D->nblock; k++) { fputs(k ? ";\n" : "", out); print_elim(D->block + k); }
            fputs("}\n\n", out);
        }
    }
    /* the normal-form check of nfname (-n): nf_NAME : PathP (<_> T) NAME NF = <_> NAME, holding iff NAME and its checker normal form
       are convertible for cubicaltt; skipped when the normal form is a literal cubicaltt would evaluate in unary, or elides an
       irrelevant component (no cubicaltt image) */
    if (nfname) for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, nfname) && needdef[i]) {
        Val *ty = force(defs[i].vty); if (ty->k != V_DATA) continue;
        Term *nf = quote(0, nf_force(defs[i].vval));
        if (unary_count(nf) < 0 || has_irr_value(nf)) { fprintf(out, "-- nf %s: skipped (a literal beyond unary, or an elided component)\n", nfname); continue; }
        const char *nm = gname(T_DEF, i); Term *T = quote(0, ty);
        fprintf(out, "nf_%s : PathP (<_> ", nm); tp(T, 0, 0, NULL); fprintf(out, ") %s ", nm); tp_arg(nf, 0, T);
        fprintf(out, " = <_> %s\n\n", nm);
    }
    if (nhole) fprintf(out, "-- eezott: %d elided irrelevant value%s printed as holes\n", nhole, nhole == 1 ? "" : "s");
    if (nirr) fputs("-- eezott: irrelevance used (cubicaltt has none: a refusal here may be the irrelevant conversion eezott allows)\n", out);
    if (nunsup) fprintf(out, "-- %d unsupported construct%s: this module is not a faithful image of the program\n", nunsup, nunsup == 1 ? "" : "s");
    return nunsup ? 3 : 0;
}
