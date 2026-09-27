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

static FILE *out;
static int nunsup, nirr, nhole;
static int id_data = -1;            /* the data type shaped like eezott's Id (params A, a; one index; refl): cubicaltt's builtin Id */
typedef struct { Term *ty; int depth, isi; } KTy;
static KTy ktys[4096];
static const char *names[4096];
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
    int lvl = depth - 1 - idx;
    if (lvl >= 0 && lvl < depth && names[lvl]) return names[lvl];
    return xsprintf("#%d", idx);
}
static void binder_open(int depth, const char *nm, Term *ty) { names[depth] = bind(depth, nm); ktys[depth].ty = ty; ktys[depth].depth = depth; ktys[depth].isi = 0; }
static void ibinder_open(int depth, const char *nm) { names[depth] = bind(depth, nm && strcmp(nm, "_") ? nm : "i"); ktys[depth].ty = NULL; ktys[depth].depth = depth; ktys[depth].isi = 1; }
/* a binder is installed after its domain is printed: the domain's own binders live at the same level (agda.c learnt this) */
static void binder_set(int depth, const char *nm, Term *ty, int isi) { names[depth] = nm; ktys[depth].ty = ty; ktys[depth].depth = depth; ktys[depth].isi = isi; }

/* ---------------- faces ---------------- */

static IVal face_iv(Term *t, int depth) {
    switch (t->k) {
    case T_I0: return iv_zero();
    case T_I1: return iv_one();
    case T_VAR: return iv_var(depth - 1 - t->n);
    case T_IAND: return iv_and(face_iv(t->a, depth), face_iv(t->b, depth));
    case T_IOR: return iv_or(face_iv(t->a, depth), face_iv(t->b, depth));
    case T_INEG: return iv_neg(face_iv(t->a, depth));
    default: unsupported("face not an interval expression"); return iv_zero();
    }
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
static void tp_arg(Term *t, int depth, Term *ty) { tp(t, depth, 4, ty); }
static int spine(Term *t, Term **args, int max);
static Term *spine_head(Term *t);

static Term *global_ty(TKind k, int id) {
    Term *ty = k == T_DEF ? defs[id].ty : k == T_DATA ? datas[id].ty : k == T_CON ? cons[id].ty : NULL;
    if (!ty) return NULL;
    return ref_poly(k, id) ? subst_hidden(ty, lv_const(0)) : ty;
}
static Term *global_val(int id) { return defs[id].poly ? subst_hidden(defs[id].val, lv_const(0)) : defs[id].val; }
/* the type of a spine's head, in the current context: closed for globals, a binder's for variables */
static Term *head_type(Term *h, int depth) {
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
        Term *args[512]; int n = spine(t, args, 512); if (n < 0) return t;
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
    Env *e = NULL; for (int l = 0; l < depth; l++) e = env_push(e, ktys[l].isi ? vivar(l) : vvar(l));
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

static int spine(Term *t, Term **args, int max) {
    int n = 0; Term *w = t;
    while (w->k == T_APP) { n++; w = w->a; }
    if (n > max) return -1;
    w = t; for (int i = n - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    return n;
}
static Term *spine_head(Term *t) { while (t->k == T_APP) t = t->a; return t; }

/* ---------------- terms ---------------- */

static void ilam_print(Term *t, int depth, int prec, Term *ty) {   /* consecutive interval lambdas: <i j> body; the body's type is the PathP's line under the binder */
    if (prec > 0) fputc('(', out);
    fputc('<', out); int d = depth;
    while (t->k == T_LAM && t->isi) {
        ty = expose(ty, d);
        ty = ty && ty->k == T_PATHP && ty->a->k == T_LAM ? ty->a->a : NULL;   /* the line's body lives under the same binder */
        ibinder_open(d, t->name); fprintf(out, "%s%s", d > depth ? " " : "", names[d]); d++; t = t->a;
    }
    fputs("> ", out); tp(t, d, 0, ty);
    if (prec > 0) fputc(')', out);
}
static void lam_print(Term *t, int depth, int prec, Term *ty) {
    if (t->isi) { ilam_print(t, depth, prec, ty); return; }
    if (prec > 0) fputc('(', out);
    fputs("\\", out); int d = depth;
    while (t->k == T_LAM && !t->isi) {
        ty = expose(ty, d);
        if (!ty || ty->k != T_PI) { unsupported("a lambda whose type the printer cannot see"); const char *nm = bind(d, t->name); fprintf(out, " (%s : ?)", nm); binder_set(d, nm, NULL, 0); d++; t = t->a; ty = NULL; continue; }
        if ((t->irr | ty->irr) & 2) nirr++;
        const char *nm = bind(d, t->name);
        fprintf(out, " (%s : ", nm); tp(ty->a, d, 0, NULL); fputc(')', out);
        binder_set(d, nm, ty->a, 0);
        d++; t = t->a; ty = ty->b;
    }
    fputs(" -> ", out); tp(t, d, 0, ty);
    if (prec > 0) fputc(')', out);
}
static void sys_sides(Term *sys, int depth, Term *elty) {   /* [ faces -> e, .. ] */
    fputc('[', out); int first = 1;
    for (int i = 0; i < sys->nbr; i++) {
        IVal f = face_iv(sys->br[i].face, depth);
        for (int c = 0; c < f.n; c++) {
            if (!conj_consistent(&f.c[c])) continue;
            fputs(first ? " " : ", ", out); first = 0;
            faces_print(&f.c[c], depth); fputs(" -> ", out);
            tp(sys->br[i].body, depth, 0, elty);
        }
    }
    fputs(first ? "]" : " ]", out);
}
/* the body of a branch whose face is total (NULL: none): on a total face Glue A [-> (T, e)] is T, glue [-> t] a is t and
   unglue b is e.1 b - cubicaltt computes these but does not check or infer the forms themselves */
static Term *total_branch(Term *sys, int depth) {
    if (!sys || sys->k != T_SYS) return NULL;
    for (int i = 0; i < sys->nbr; i++) if (iv_is_one(face_iv(sys->br[i].face, depth))) return sys->br[i].body;
    return NULL;
}
/* eezott's e : Equiv T A (fiber f x = y) flipped into the kernel's shape (fiber x = f y): eqvFlip T A e */
static void equiv_flip(Term *T, Term *A, Term *e, int depth) {
    fputs("eqvFlip ", out); tp_arg(T, depth, NULL); fputc(' ', out); tp_arg(A, depth, NULL); fputc(' ', out); tp_arg(e, depth, NULL);
}
static void glue_sides(Term *Te, Term *A, int depth) {   /* [ faces -> (T, eqvFlip T A e) ] */
    if (Te->k != T_SYS) { unsupported("a Glue system that is not written as a system"); return; }
    fputc('[', out); int first = 1;
    for (int i = 0; i < Te->nbr; i++) {
        IVal f = face_iv(Te->br[i].face, depth);
        for (int c = 0; c < f.n; c++) {
            if (!conj_consistent(&f.c[c])) continue;
            fputs(first ? " " : ", ", out); first = 0;
            faces_print(&f.c[c], depth); fputs(" -> ", out);
            Term *b = Te->br[i].body;
            Term *T = b->k == T_PAIR ? b->a : mk_term(T_FST, b, NULL, NULL, NULL), *e = b->k == T_PAIR ? b->b : mk_term(T_SND, b, NULL, NULL, NULL);
            fputc('(', out); tp(T, depth, 0, NULL); fputs(", ", out); equiv_flip(T, A, e, depth); fputc(')', out);
        }
    }
    fputs(first ? "]" : " ]", out);
}
/* a cube constructor's method as written, \is -> inS t: the element t under the same lambdas (its type is the nested PathP) */
static Term *strip_ins(Term *m) {
    if (m->k == T_LAM) { Term *b = strip_ins(m->a); if (!b) return NULL; Term *r = mk_lam(m->name, b, m->irr); r->isi = m->isi; return r; }
    if (m->k == T_INS) return m->a;
    return NULL;
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
    if (n == 0) return ty;
    int v = n - 1;
    Term *b0 = branch_at(br, nbr, v, 0, depth), *b1 = branch_at(br, nbr, v, 1, depth);
    if (!b0 || !b1) return NULL;
    Term *inner = cube(ty, br, nbr, n - 1, depth);
    if (!inner) return NULL;
    Term *line = mk_lam("i", inner, 0); line->isi = 1;
    Term *e0 = subst_term(b0, v, I0), *e1 = subst_term(b1, v, I1);
    for (int q = n - 2; q >= 0; q--) { e0 = mk_lam("j", e0, 0); e0->isi = 1; e1 = mk_lam("j", e1, 0); e1->isi = 1; }
    return mk_term(T_PATHP, line, e0, e1, NULL);
}
static Term *fix_method(Term *mt, int depth) {
    if (mt->k == T_PI && !(mt->isi || mt->a->k == T_INTERVAL)) { Term *r = mk_pi(mt->name, mt->a, fix_method(mt->b, depth + 1), mt->irr); r->isi = mt->isi; return r; }
    int n = 0; Term *w = mt;
    while (w->k == T_PI && (w->isi || w->a->k == T_INTERVAL)) { n++; w = w->b; }
    if (n == 0) return mt;
    if (w->k == T_SUB && w->c->k == T_SYS) { Term *c = cube(w->a, w->c->br, w->c->nbr, n, depth + n); if (c) return c; unsupported("a cube method whose boundary is not a full cube"); return mt; }
    if (w->k == T_PATHP) return mt;
    unsupported("an interval-binder method without a boundary"); return mt;
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
static int pre_type(Term *t) {
    if (!t) return 0;
    switch (t->k) {
    case T_PI: return t->isi || t->pre || t->a->k == T_INTERVAL || pre_type(t->a) || pre_type(t->b);
    case T_PARTIAL: case T_SUB: case T_INTERVAL: case T_LEVEL: return 1;
    case T_U: return t->pre;
    case T_SYS: return 0;
    default: return pre_type(t->a) || pre_type(t->b) || pre_type(t->c) || pre_type(t->d);
    }
}
static int inline_def(int id) { return pre_type(global_ty(T_DEF, id)); }

/* head reduction of what cubicaltt cannot name: a beta redex (comp's desugaring, an unfolded definition applied),
   outS (inS a), and a definition of a pretype at its use. The rest of the program is printed as written. */
static Term *red(Term *t) {
    for (;;) {
        if (t->k == T_DEF && inline_def(t->n)) { t = global_val(t->n); continue; }
        if (t->k == T_OUTS) { Term *d = red(t->d); if (d->k == T_INS) { t = d->a; continue; } return t; }
        if (t->k == T_PAPP) { Term *p = red(t->a); if (p->k == T_LAM && p->isi) { t = inst_tele(p->a, 1, &t->b, 0); continue; } return t; }
        if (t->k != T_APP) return t;
        Term *args[512]; int n = spine(t, args, 512); if (n < 0) return t;
        Term *h = spine_head(t), *hr = red(h);
        if (hr->k != T_LAM) return t;
        Term *v = hr; int i = 0;
        for (; i < n && v->k == T_LAM; i++) v = inst_tele(v->a, 1, &args[i], 0);
        for (; i < n; i++) v = mk_app(v, args[i], 0);
        t = v;
    }
}

static void app_print(Term *t, int depth, int prec, Term *ty) {
    Term *args[512]; int n = spine(t, args, 512);
    if (n < 0) { unsupported("spine too long"); return; }
    Term *h = spine_head(t);
    /* the Id shape: the builtin */
    if (h->k == T_DATA && h->n == id_data && n == 3) { if (prec > 3) fputc('(', out); fputs("Id ", out); tp_arg(args[0], depth, NULL); fputc(' ', out); tp_arg(args[1], depth, NULL); fputc(' ', out); tp(args[2], depth, 3, NULL); if (prec > 3) fputc(')', out); return; }
    if (h->k == T_CON && cons[h->n].data == id_data && n == 2) { if (prec > 3) fputc('(', out); fputs("idC (<_> ", out); tp(args[1], depth, 0, NULL); fputs(") [ -> ", out); tp(args[1], depth, 0, NULL); fputs(" ]", out); if (prec > 3) fputc(')', out); return; }
    if (h->k == T_ELIM && h->n == id_data) {
        if (n < 6) { unsupported("elim Id not fully applied"); return; }
        if (prec > 2 || (prec > 3 && n == 6)) fputc('(', out);
        if (n > 6) fputc('(', out);
        fputs("idJ", out);
        Term *ety = head_type(h, depth);
        for (int i = 0; i < n; i++) { fputc(' ', out); Term *dom = ety && ety->k == T_PI ? ety->a : NULL; tp_arg(args[i], depth, dom); ety = pi_apply(ety, args[i], depth); if (i == 5 && n > 6) fputc(')', out); }
        if (prec > 2 || (prec > 3 && n == 6)) fputc(')', out);
        return;
    }
    int nint = 0, neta = 0, np = 0, nargs = 0;   /* a path constructor's missing intervals; a constructor's missing arguments (eta-expanded: cubicaltt checks a constructor against its data type only) */
    if (h->k == T_CON) { Con *C = &cons[h->n]; np = datas[C->data].nparams; nargs = C->nargs; if (C->nint && n < np + nargs + C->nint) nint = np + nargs + C->nint - n; if (!C->nint && n < np + nargs) neta = np + nargs - n; }
    if (nint && n < np + nargs) { unsupported("a path constructor partially applied before its interval arguments"); nint = 0; }
    int m = nint + neta, d2 = depth + m;
    int paren = m ? prec > 0 : (prec > 2 && n > 0);
    if (paren) fputc('(', out);
    if (nint) { fputc('<', out); for (int q = 0; q < nint; q++) { ibinder_open(depth + q, xsprintf("i%d", q)); fprintf(out, "%s%s", q ? " " : "", names[depth + q]); } fputs("> ", out); }
    if (neta) {   /* \ (a : A) .. -> c args.. a ..: the binder types from the head's type at the given arguments */
        Term *etas = head_type(h, depth);
        for (int i = 0; i < n; i++) etas = pi_apply(etas, args[i], depth);
        fputs("\\", out);
        for (int k = 0; k < neta; k++) {
            Term *ex = expose(etas, depth + k);
            if (!ex || ex->k != T_PI) { unsupported("the type of a constructor's missing argument"); break; }
            const char *nm = bind(depth + k, ex->name);
            fprintf(out, " (%s : ", nm); tp(ex->a, depth + k, 0, NULL); fputc(')', out);
            binder_set(depth + k, nm, ex->a, 0); etas = ex->b;
        }
        fputs(" -> ", out);
    }
    if (m) { t = shift(t, 0, m); n = spine(t, args, 512); h = spine_head(t); }   /* the given arguments, under the new binders */
    Term *hty = head_type(h, d2);
    switch (h->k) {
    case T_CON: {
        Con *C = &cons[h->n];
        if (C->nint) {   /* a path constructor: c{D p..} a.. @ i.. */
            fprintf(out, "%s{%s", gname(T_CON, h->n), gname(T_DATA, C->data));
            for (int i = 0; i < np && i < n; i++) { fputc(' ', out); tp_arg(args[i], d2, NULL); }
            fputc('}', out);
        } else fputs(gname(T_CON, h->n), out);
        break; }
    case T_DEF: case T_DATA: case T_ELIM: fputs(gname(h->k, h->n), out); break;
    default: tp(h, d2, 2, NULL); break;
    }
    for (int i = 0; i < n; i++) {
        Term *ex = expose(hty, d2);
        Term *dom = ex && ex->k == T_PI ? ex->a : NULL;
        int isint = ex && ex->k == T_PI && (ex->isi || ex->a->k == T_INTERVAL);
        if (ex && ex->k == T_PI && (ex->irr & 2)) nirr++;
        if (h->k == T_CON && (i < np)) { hty = pi_apply(hty, args[i], d2); continue; }   /* a constructor's parameters: cubicaltt infers them (or they went into the braces) */
        if (isint) { fputs(" @ ", out); tp(args[i], d2, 5, NULL); }
        else if (is_cube_method_arg(h, i)) { Term *m = strip_ins(args[i]); fputc(' ', out); if (m) tp_arg(m, d2, dom ? fix_method(dom, d2) : NULL); else { unsupported("a cube method not of the form \\is -> inS t"); tp_arg(args[i], d2, NULL); } }   /* typed by the method's nested-PathP form: its element binders, then the interval lambdas along the PathP lines */
        else { fputc(' ', out); tp_arg(args[i], d2, dom); }
        hty = pi_apply(hty, args[i], d2);
    }
    for (int q = 0; q < neta; q++) fprintf(out, " %s", names[depth + q]);
    for (int q = 0; q < nint; q++) fprintf(out, " @ %s", names[depth + q]);
    if (paren) fputc(')', out);
}

/* the sides of an hComp: every branch of sys (under [.., j], j the composition's direction named jn) whose face is conjoined
   with ctx; a branch whose body reduces to a system (a filler's partial element applied) contributes its own branches under
   the conjoined face */
static void hc_sides(Term *sys, IVal ctx, int depth, const char *jn, Term *elty, int *first) {
    for (int i = 0; i < sys->nbr; i++) {
        IVal f = iv_and(ctx, face_iv(sys->br[i].face, depth));
        Term *body = red(sys->br[i].body);
        if (body->k == T_SYS) { hc_sides(body, f, depth, jn, elty, first); continue; }
        for (int c = 0; c < f.n; c++) {
            if (!conj_consistent(&f.c[c])) continue;
            int mentions_j = 0; for (int l = 0; l < f.c[c].n; l++) if (f.c[c].l[l].var == depth - 1) mentions_j = 1;
            if (mentions_j) { unsupported("a face mentioning the composition's own direction"); continue; }
            fputs(*first ? " " : ", ", out); *first = 0;
            faces_print(&f.c[c], depth); fprintf(out, " -> <%s> ", jn);
            tp(body, depth, 0, elty);
        }
    }
}

static void tp(Term *t, int depth, int prec, Term *ty) {
    if (!t) { fputs("?", out); return; }
    t = red(t);
    if ((t->k == T_APP || t->k == T_CON || t->k == T_NUM) && peano_print(t)) return;
    switch (t->k) {
    case T_VAR: fputs(vname(depth, t->n), out); break;
    case T_U: if (t->pre) unsupported("the sort of pretypes"); else fputs("U", out); break;
    case T_LEVEL: case T_LZERO: case T_LSUC: case T_LMAX: case T_LVAL: case T_LMETA: unsupported("a universe level"); break;
    case T_META: unsupported("unsolved meta"); break;
    case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_APP: app_print(t, depth, prec, ty); break;
    case T_NUM: unsupported("a literal of a type not shaped like the naturals"); break;
    case T_IRR: fputc('?', out); nhole++; break;   /* an elided irrelevant value (a word's proof component): a hole, which cubicaltt checks trivially, as eezott never compares it */
    case T_INTERVAL: unsupported("the interval as a type"); break;
    case T_I0: fputs("0", out); break;
    case T_I1: fputs("1", out); break;
    case T_INEG: fputc('-', out); if (t->a->k == T_INEG) { fputc('(', out); tp(t->a, depth, 0, NULL); fputc(')', out); } else tp(t->a, depth, 5, NULL); break;   /* never --: a line comment */
    case T_IAND: fputc('(', out); tp(t->a, depth, 0, NULL); fputs(" /\\ ", out); tp(t->b, depth, 0, NULL); fputc(')', out); break;
    case T_IOR: fputc('(', out); tp(t->a, depth, 0, NULL); fputs(" \\/ ", out); tp(t->b, depth, 0, NULL); fputc(')', out); break;
    case T_PI: {
        if (t->isi || t->a->k == T_INTERVAL) { unsupported("a function over the interval"); break; }
        if (t->irr & 2) nirr++;
        if (prec > 1) fputc('(', out);
        int dep = term_mentions_var(t->b, 0);
        if (!dep) { tp(t->a, depth, 2, NULL); fputs(" -> ", out); binder_open(depth, "_", t->a); }
        else { const char *nm = bind(depth, t->name); fprintf(out, "(%s : ", nm); tp(t->a, depth, 0, NULL); fputs(") -> ", out); binder_set(depth, nm, t->a, 0); }
        tp(t->b, depth + 1, 1, NULL);
        if (prec > 1) fputc(')', out);
        break; }
    case T_SIGMA: {
        if (t->irr) nirr++;
        if (prec > 1) fputc('(', out);
        { const char *nm = bind(depth, t->name); fprintf(out, "(%s : ", nm); tp(t->a, depth, 0, NULL); fputs(") * ", out); binder_set(depth, nm, t->a, 0); }
        tp(t->b, depth + 1, 1, NULL);
        if (prec > 1) fputc(')', out);
        break; }
    case T_PAIR: {
        Term *ex = expose(ty, depth);
        Term *ta = ex && ex->k == T_SIGMA ? ex->a : NULL, *tb = ex && ex->k == T_SIGMA ? inst_tele(ex->b, 1, &t->a, 0) : NULL;
        if (t->irr) nirr++;
        fputc('(', out); tp(t->a, depth, 0, ta); fputs(", ", out); tp(t->b, depth, 0, tb); fputc(')', out); break; }
    case T_FST: if (prec > 4) fputc('(', out); tp(t->a, depth, 4, NULL); fputs(".1", out); if (prec > 4) fputc(')', out); break;
    case T_SND: if (prec > 4) fputc('(', out); tp(t->a, depth, 4, NULL); fputs(".2", out); if (prec > 4) fputc(')', out); break;
    case T_LAM: lam_print(t, depth, prec, ty); break;
    case T_LET: {
        if (pre_type(t->a)) { tp(inst_tele(t->c, 1, &t->b, 0), depth, prec, ty); break; }   /* a let of a pretype (lemIso's fillers): unfolded at its uses */
        if (prec > 0) fputc('(', out);
        if (t->irr & 2) nirr++;
        /* layout, not braces: the stop word 'in' would close the module's implicit block past an explicit one (BNFC's resolver) */
        { const char *nm = bind(depth, t->name); fprintf(out, "let %s : ", nm); tp(t->a, depth, 0, NULL); fputs(" = ", out); tp(t->b, depth, 0, t->a); fputs(" in ", out); binder_set(depth, nm, t->a, 0); }
        tp(t->c, depth + 1, 0, ty ? shift(ty, 0, 1) : NULL);
        if (prec > 0) fputc(')', out);
        break; }
    case T_PATHP: {
        if (prec > 3) fputc('(', out);
        fputs("PathP ", out); tp_arg(t->a, depth, NULL); fputc(' ', out);
        tp_arg(t->b, depth, line_at(t->a, I0)); fputc(' ', out); tp_arg(t->c, depth, line_at(t->a, I1));
        if (prec > 3) fputc(')', out);
        break; }
    case T_PAPP: if (prec > 2) fputc('(', out); tp(t->a, depth, 2, NULL); fputs(" @ ", out); tp(t->b, depth, 5, NULL); if (prec > 2) fputc(')', out); break;
    case T_PARTIAL: case T_SYS: case T_SUB: case T_INS: unsupported("a partial element, a Sub type or inS outside hcomp/Glue/a cube method"); break;
    case T_OUTS: {
        Term *h = t->d; while (h->k == T_APP || h->k == T_PAPP) h = h->a;
        if (h->k == T_VAR) { int lvl = depth - 1 - h->n; Term *kt = (lvl >= 0 && lvl < depth) ? ktys[lvl].ty : NULL; if (kt && kt->k == T_PATHP) { tp(t->d, depth, prec, ty); break; } }   /* the element of a cube method: the method is the path itself */
        unsupported("outS"); break; }
    case T_TRANSP: {   /* comp (<i> L) u0 [ faces(phi) -> <_> u0 ] */
        if (prec > 3) fputc('(', out);
        fputs("comp ", out); tp_arg(t->a, depth, NULL); fputc(' ', out); tp_arg(t->c, depth, line_at(t->a, I0)); fputc(' ', out);
        IVal phi = face_iv(t->b, depth); fputc('[', out); int first = 1;
        for (int c = 0; c < phi.n; c++) { if (!conj_consistent(&phi.c[c])) continue; fputs(first ? " " : ", ", out); first = 0; faces_print(&phi.c[c], depth); fputs(" -> <_> ", out); tp(t->c, depth, 0, NULL); }
        fputs(first ? "]" : " ]", out);
        if (prec > 3) fputc(')', out);
        break; }
    case T_HCOMP: {   /* comp (<_> A) u0 [ faces -> <j> t ]: hcomp is composition along the constant line (CCHM); cubicaltt's own hComp
                         is a stuck value on every type, its comp computes on data, in U and along the lines composed there */
        Term *u = red(t->c);
        Term *sys = u->k == T_LAM && u->isi ? red(u->a) : NULL;
        if (!sys || sys->k != T_SYS) { unsupported("an hcomp whose system is not written as one"); break; }
        if (prec > 3) fputc('(', out);
        fputs("comp (<_> ", out); tp(t->a, depth, 0, NULL); fputs(") ", out); tp_arg(t->d, depth, t->a); fputc(' ', out);
        ibinder_open(depth, u->name);
        fputc('[', out); int first = 1;
        hc_sides(sys, iv_one(), depth + 1, names[depth], shift(t->a, 0, 1), &first);
        fputs(first ? "]" : " ]", out);
        if (prec > 3) fputc(')', out);
        break; }
    case T_GLUE: {
        Term *tot = total_branch(t->c, depth);
        if (tot) { tp(tot->k == T_PAIR ? tot->a : mk_term(T_FST, tot, NULL, NULL, NULL), depth, prec, ty); break; }
        if (prec > 3) fputc('(', out);
        fputs("Glue ", out); tp_arg(t->a, depth, NULL); fputc(' ', out); glue_sides(t->c, t->a, depth);
        if (prec > 3) fputc(')', out);
        break; }
    case T_GLUEEL: {
        Term *tot = total_branch(t->a, depth);
        if (tot) { tp(tot, depth, prec, ty); break; }
        if (prec > 3) fputc('(', out);
        fputs("glue ", out); tp_arg(t->b, depth, t->c && t->c->k == T_GLUE ? t->c->a : NULL); fputc(' ', out);
        if (t->a->k == T_SYS) sys_sides(t->a, depth, NULL); else unsupported("a glue system that is not written as one");
        if (prec > 3) fputc(')', out);
        break; }
    case T_UNGLUE: {
        Term *tot = total_branch(t->d, depth);
        if (tot) { Term *e = tot->k == T_PAIR ? tot->b : mk_term(T_SND, tot, NULL, NULL, NULL); tp(mk_app(mk_term(T_FST, e, NULL, NULL, NULL), t->a, 0), depth, prec, ty); break; }
        if (prec > 3) fputc('(', out);
        Term *b = red(t->a);
        fputs("unglue ", out);
        if (b->k == T_GLUEEL || b->k == T_PAIR || b->k == T_LAM || b->k == T_CON) {   /* cubicaltt infers unglue's argument: what it only checks is ascribed its Glue type */
            fputs("(asc ", out); tp_arg(mk_term(T_GLUE, t->b, t->c, t->d, NULL), depth, NULL); fputc(' ', out); tp_arg(b, depth, NULL); fputc(')', out);
        } else tp_arg(b, depth, NULL);
        fputc(' ', out); glue_sides(t->d, t->b, depth);
        if (prec > 3) fputc(')', out);
        break; }
    }
}

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
static void need_term(Term *t);
static void need_data(int d) {
    Data *D = &datas[d]; if (needdata[d]) return;
    for (int k = 0; k < D->nblock; k++) {
        int m = D->block + k; if (needdata[m]) continue; needdata[m] = 1;
        Data *M = &datas[m];
        for (int i = 0; i < M->nparams; i++) need_term(M->ptys[i]);
        for (int j = 0; j < M->nidx; j++) need_term(M->itys[j]);
        for (int ci = 0; ci < M->ncons; ci++) { Con *C = &cons[M->cons[ci]]; for (int j = 0; j < C->nargs; j++) need_term(C->args[j].ty); for (int j = 0; j < M->nidx; j++) need_term(C->ridx[j]); if (C->boundary) need_term(C->boundary); }
    }
}
static void need_def(int i) { if (needdef[i]) return; needdef[i] = 1; need_term(defs[i].ty); need_term(defs[i].val); }
static void need_term(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF: need_def(t->n); return;
    case T_DATA: case T_ELIM: need_data(t->n); return;
    case T_CON: need_data(cons[t->n].data); return;
    case T_NUM: need_data(t->n); return;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { need_term(t->br[i].face); need_term(t->br[i].body); } return;
    default: need_term(t->a); need_term(t->b); need_term(t->c); need_term(t->d); return;
    }
}
static int has_irr_value(Term *t) {
    if (!t) return 0;
    if (t->k == T_IRR) return 1;
    if (t->k == T_SYS) { for (int i = 0; i < t->nbr; i++) if (has_irr_value(t->br[i].face) || has_irr_value(t->br[i].body)) return 1; return 0; }
    return has_irr_value(t->a) || has_irr_value(t->b) || has_irr_value(t->c) || has_irr_value(t->d);
}

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
