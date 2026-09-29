/*
 * agda.c - eezott -A: the elaborated program printed as Cubical Agda (M20, F1).
 *
 * The differential test's first oracle is Agda's --cubical mode, whose primitives are eezott's
 * (transp, hcomp, Glue, Partial, Sub, a De Morgan interval).  This file prints the checked program -
 * the elaborated core terms, exactly the judgement the kernel made - as one Agda module that uses
 * only Agda's builtin modules, so that `agda --cubical` re-checks every definition independently.
 *
 *   data types     -> data declarations (a mutual block: signatures first, then the constructors)
 *   elim D         -> a function elimˍD defined by pattern matching, its type eezott's own (elim_type)
 *   path constructors and their methods -> PathP (nested for cubes); Agda has no other form
 *   Sigma A .B     -> a record with an irrelevant second field (Σᵢ, declared in the header)
 *   Glue           -> primGlue with the types and the equivalences as two systems, eezott's Equiv
 *                     (a Sigma) coerced into Agda's isEquiv record at the site
 *   a partial element used as an element on a face that holds (elab's silent coercion) -> applied to 1=1
 *   levels         -> Level; a polymorphic global takes its hidden level as a first explicit argument
 *
 * What Agda cannot say is reported, not approximated: a path constructor whose boundary is not a full
 * cube, an interval-binder constructor without a boundary.  The printer then leaves a comment
 * `-- UNSUPPORTED: ...` and exits 3, so that the harness files the case as inexpressible rather
 * than as a disagreement.
 */
#include "tt.h"
#include "machine.h"

static FILE *out;
static int nunsup;
static const char *ownlvl;          /* the name of the hidden level of the global being printed (NULL: none) */
static int nat_builtin = -1;        /* the data type declared BUILTIN NATURAL (the first shaped like the naturals) */

/* a binder's known type: the term and the depth it lives at (for the 1=1 coercion) */
typedef struct { Term *ty; int depth; } KTy;
/* the binders in scope, by level: grown (zero-filled) to any level the printer reaches */
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
static const char **nm_at(int i) { kgrow(i); return &names[i]; }
static KTy *kt_at(int i) { kgrow(i); return &ktys[i]; }
#define NM(i) (*nm_at(i))
#define KT(i) (*kt_at(i))
static char *needdef, *needdata;   /* the declarations the program reaches (agda_program) */

static void unsupported(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    fputs("{- UNSUPPORTED: ", out); vfprintf(out, fmt, ap); fputs(" -}", out);
    va_end(ap); nunsup++;
}

/* ---------------- names ---------------- */

static const char *reserved[] = {
    "I", "i0", "i1", "IsOne", "Partial", "PartialP", "isOneEmpty", "transp", "hcomp", "PathP", "Sub", "inS", "outS", "G",
    "Σ", "Σᵢ", "fst", "snd", "fstᵢ", "sndᵢ", "Level", "lzero", "lsuc", "Set", "SSet", "Prop", "Setω", "Agda", "Nat′",
    "abstract", "codata", "coinductive", "constructor", "data", "do", "eta-equality", "field", "forall", "hiding", "import",
    "in", "inductive", "infix", "infixl", "infixr", "instance", "interleaved", "let", "macro", "module", "mutual",
    "no-eta-equality", "opaque", "open", "overlap", "pattern", "postulate", "primitive", "private", "public", "quote",
    "quoteTerm", "record", "renaming", "rewrite", "syntax", "tactic", "to", "unfolding", "unquote", "unquoteDecl",
    "unquoteDef", "using", "variable", "where", "with", "1=1", NULL };
static int is_reserved(const char *s) { for (int i = 0; reserved[i]; i++) if (!strcmp(s, reserved[i])) return 1; return 0; }
static int is_global(const char *s) {
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, s)) return 1;
    for (int i = 0; i < ndatas; i++) if (!strcmp(datas[i].name, s)) return 1;
    for (int i = 0; i < ncons; i++) if (!strcmp(cons[i].name, s)) return 1;
    return 0;
}
/* an eezott identifier as an Agda one: '_' is a mixfix hole in Agda, so it becomes a low macron; reserved words get a prime */
static const char *mangle(const char *s) {
    size_t n = strlen(s); char *r = xalloc(3 * n + 4); char *p = r;
    for (const char *q = s; *q; q++) { if (*q == '_') { memcpy(p, "ˍ", 2); p += 2; } else if (*q == '{' || *q == '}') continue; else *p++ = *q; }   /* elab names an inserted implicit binder "{x}" */
    *p = 0;
    if (is_reserved(r)) { memcpy(p, "′", 3); p += 3; *p = 0; }
    return r;
}
static const char *gname(TKind k, int id) {
    switch (k) {
    case T_DEF: return mangle(defs[id].name);
    case T_DATA: return mangle(datas[id].name);
    case T_CON: return mangle(cons[id].name);
    case T_ELIM: return xsprintf("elimˍ%s", mangle(datas[id].name));
    default: return "?";
    }
}
/* a binder name unique among the globals, the reserved words and the binders in scope */
static const char *bind(int depth, const char *nm) {
    if (!nm || !strcmp(nm, "_")) return "_";
    const char *r = mangle(nm);
    for (;;) {
        int clash = is_global(r) || is_reserved(r);
        for (int i = 0; i < depth && !clash; i++) if (NM(i) && !strcmp(NM(i), r)) clash = 1;
        if (!clash) return r;
        r = xsprintf("%s′", r);
    }
}
static const char *vname(int depth, int idx) {
    int lvl = depth - 1 - idx;
    if (lvl >= 0 && lvl < depth && NM(lvl)) return NM(lvl);
    return xsprintf("#%d", idx);
}

/* ---------------- levels ---------------- */

static void tp(Term *t, int depth, int prec);
static void tp_arg(Term *t, int depth);
static void implicit_level(const char *name, Term *l, int depth);
/* an element of the max-plus algebra as an Agda level */
static void lv_print(LVal l, int depth, int prec) {
    int nparts = l.n + (l.c > 0 || l.n == 0 ? 1 : 0);
    int compound = nparts > 1 || (l.n == 1 && l.t[0].off > 0) || (l.n == 0 && l.c > 0);   /* an application (lsuc ..) or a join */
    if (compound && prec > 0) fputc('(', out);
    for (int i = 0; i < l.n; i++) {
        if (i) fputs(" ⊔ ", out);
        for (int q = 0; q < l.t[i].off; q++) fputs("lsuc (", out);
        if (l.t[i].meta) unsupported("level meta ?%d", l.t[i].var);
        else if (l.t[i].var == -1) fputs(ownlvl ? ownlvl : "lzero", out);
        else fputs(vname(depth, depth - 1 - l.t[i].var), out);
        for (int q = 0; q < l.t[i].off; q++) fputc(')', out);
    }
    if (l.c > 0 || l.n == 0) {
        if (l.n) fputs(" ⊔ ", out);
        for (int q = 0; q < l.c; q++) fputs("lsuc (", out);
        fputs("lzero", out);
        for (int q = 0; q < l.c; q++) fputc(')', out);
    }
    if (compound && prec > 0) fputc(')', out);
}
static void lv_const_print(int n, int prec) {
    if (n && prec > 0) fputc('(', out);
    for (int q = 0; q < n; q++) fputs("lsuc (", out);
    fputs("lzero", out);
    for (int q = 0; q < n; q++) fputc(')', out);
    if (n && prec > 0) fputc(')', out);
}
/* a level term */
/* the level a polymorphic global reference is taken at (its first explicit argument) */

/* ---------------- the interval and faces ---------------- */

/* a face term to the free De Morgan algebra (variables by level) */
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
/* the clauses of a partial element: one per consistent conjunct of each branch's face */
static int conj_consistent(IConj *c) {
    for (int i = 0; i < c->n; i++) for (int j = i + 1; j < c->n; j++) if (c->l[i].var == c->l[j].var && c->l[i].neg != c->l[j].neg) return 0;
    return 1;
}

/* ---------------- the 1=1 coercion ---------------- */

/* the type of a term when it is a variable, a global or an application of one, peeled of the applied arguments' binders;
   NULL when unknown. Only the outermost shape matters: is it Partial? */
static Term *head_type(Term *t, int depth, int *nargs) {
    int n = 0;
    while (t->k == T_APP) { n++; t = t->a; }
    *nargs = n;
    if (t->k == T_VAR) { int lvl = depth - 1 - t->n; return (lvl >= 0 && lvl < depth) ? KT(lvl).ty : NULL; }
    if (t->k == T_DEF) return defs[t->n].ty;
    return NULL;
}
static int is_partial_element(Term *t, int depth) {
    int n; Term *ty = head_type(t, depth, &n);
    if (!ty) return 0;
    while (n > 0 && ty->k == T_PI) { ty = ty->b; n--; }
    while (n > 0 && ty->k == T_LET) { ty = ty->c; }
    return n == 0 && ty->k == T_PARTIAL;
}

/* ---------------- cubes: boundaries as nested PathP ---------------- */

/* the branch of a boundary system whose face is the literal 'variable idx = e' (NULL: none) */
static Term *branch_at(TBranch *br, int nbr, int idx, int e, int depth) {
    IVal want = e ? iv_var(depth - 1 - idx) : iv_neg(iv_var(depth - 1 - idx));
    for (int i = 0; i < nbr; i++) if (iv_eq(face_iv(br[i].face, depth), want)) return br[i].body;
    return NULL;
}
/* ty and the branches live under [outer, i_0 .. i_{n-1}] (depth counts them); the nested PathP under [outer], NULL if
   the boundary is not a full cube */
static Term *cube(Term *ty, TBranch *br, int nbr, int n, int depth) {
    /* the branches looked up from i_0 in (the recursion's order), the PathP built from the inside */
    Term **b0 = xalloc((n + 1) * sizeof(Term *)), **b1 = xalloc((n + 1) * sizeof(Term *));
    for (int v = n - 1; v >= 0; v--) {
        b0[v] = branch_at(br, nbr, v, 0, depth); b1[v] = branch_at(br, nbr, v, 1, depth);
        if (!b0[v] || !b1[v]) return NULL;
    }
    Term *inner = ty;
    for (int m = 1; m <= n; m++) {
        int v = m - 1;
        Term *line = mk_lam("i", inner, 0); line->isi = 1;
        Term *e0 = subst_term(b0[v], v, mk_term(T_I0, NULL, NULL, NULL, NULL)), *e1 = subst_term(b1[v], v, mk_term(T_I1, NULL, NULL, NULL, NULL));
        for (int q = m - 2; q >= 0; q--) { e0 = mk_lam("j", e0, 0); e0->isi = 1; e1 = mk_lam("j", e1, 0); e1->isi = 1; }
        inner = mk_term(T_PATHP, line, e0, e1, NULL);
    }
    return inner;
}
/* a method's type from elim_type, its cube form (is : I) -> Sub (P (c a is)) phi [faces -> E(boundary)] rewritten as the
   nested PathP; other shapes returned as they are */
static Term *fix_method(Term *mt0, int depth0) {
    int k = 0; Term *mt = mt0;
    while (mt->k == T_PI && !(mt->isi || mt->a->k == T_INTERVAL)) { k++; mt = mt->b; }
    Term **ps = xalloc((k + 1) * sizeof(Term *)); { Term *w = mt0; for (int i = 0; i < k; i++) { ps[i] = w; w = w->b; } }
    int depth = depth0 + k;
    Term *r;
    int n = 0; Term *w = mt;
    while (w->k == T_PI && (w->isi || w->a->k == T_INTERVAL)) { n++; w = w->b; }
    if (n == 0) r = mt;
    else if (w->k == T_SUB && w->c->k == T_SYS) {
        Term *c = cube(w->a, w->c->br, w->c->nbr, n, depth + n);
        if (c) r = c; else { unsupported("a cube method whose boundary is not a full cube"); r = mt; }
    }
    else if (w->k == T_PATHP) r = mt;
    else { unsupported("an interval-binder method without a boundary"); r = mt; }
    for (int i = k - 1; i >= 0; i--) { Term *p = mk_pi(ps[i]->name, ps[i]->a, r, ps[i]->irr); p->imp = ps[i]->imp; p->isi = ps[i]->isi; p->pre = ps[i]->pre; r = p; }
    return r;
}

/* ---------------- the universe level of a type term (for Agda's implicit levels, which cumulativity leaves unsolved) ---------------- */

static Term *lvl_const(int n) { Term *t = mk_term(T_LZERO, NULL, NULL, NULL, NULL); t->n = n; return t; }
static Term *lvl_suc(Term *l, int n) { if (!l) return NULL; if (n == 0) return l; Term *t = mk_term(T_LSUC, l, NULL, NULL, NULL); t->n = n; return t; }
static Term *lvl_max(Term *a, Term *b) { if (!a || !b) return NULL; return mk_term(T_LMAX, a, b, NULL, NULL); }
/* the level of a global taken at ref level r: its declared level hidden+n (poly) or a constant */
static Term *global_level_at(LVal lvl, int poly, Term *ref) {
    int hn, c;
    if (lv_is_hidden_plus(lvl, &hn)) { if (!poly) return lvl_const(hn); return lvl_suc(ref->a ? ref->a : lvl_const(0), hn); }
    if (lv_is_const(lvl, &c)) return lvl_const(c);
    return NULL;
}
static Term *u_level(Term *u) {   /* the level of U l as a type: lsuc l */
    if (u->a) return lvl_suc(u->a, 1);
    return lvl_const(u->n + 1);
}
/* the universe level of a type term; iterative: a max waits for both sides (the left first), a tail case continues */
typedef struct { Term *t; int depth, post; } TLItem;
static Stack tlst = { NULL, 0, 0, sizeof(TLItem) }, tlvst = { NULL, 0, 0, sizeof(Term *) };
static Term *type_level(Term *t0, int depth0) {
    size_t ib = tlst.n;
    TLItem it0 = { t0, depth0, 0 }; STACK_PUSH(&tlst, TLItem, it0);
    while (tlst.n > ib) {
        TLItem it = STACK_POP(&tlst, TLItem);
        if (it.post) { Term *b = STACK_POP(&tlvst, Term *), *a = STACK_POP(&tlvst, Term *); STACK_PUSH(&tlvst, Term *, lvl_max(a, b)); continue; }
        Term *t = it.t; int depth = it.depth, again = 1, pushed = 0; Term *r = NULL;
        while (again) {
            again = 0;
            if (!t) { r = NULL; break; }
            switch (t->k) {
            case T_U: r = u_level(t); break;
            case T_PI: case T_SIGMA:
                if (t->k == T_PI && (t->isi || t->a->k == T_INTERVAL || t->a->k == T_LEVEL)) { t = t->b; depth++; again = 1; break; }
                {   TLItem p = { NULL, 0, 1 }, b = { t->b, depth + 1, 0 }, a = { t->a, depth, 0 };
                    STACK_PUSH(&tlst, TLItem, p); STACK_PUSH(&tlst, TLItem, b); STACK_PUSH(&tlst, TLItem, a); pushed = 1; }
                break;
            case T_PATHP: if (t->a->k == T_LAM) { t = t->a->a; depth++; again = 1; } else r = NULL; break;
            case T_PARTIAL: t = t->b; again = 1; break;
            case T_SUB: t = t->a; again = 1; break;
            case T_GLUE: r = t->d ? t->d : lvl_const(t->n); break;
            case T_VAR: { int lvl = depth - 1 - t->n; Term *kt = (lvl >= 0 && lvl < depth) ? KT(lvl).ty : NULL;
                r = NULL;
                if (kt && kt->k == T_U) { if (!kt->a) r = lvl_const(kt->n); else if (kt->a->k == T_LVAL || kt->a->k == T_LZERO) r = kt->a; }
                break; }
            case T_DATA: r = global_level_at(datas[t->n].lvl, datas[t->n].poly, t); break;
            case T_APP: case T_DEF: {
                if (t->k == T_APP && t->a->k == T_LAM) { t = subst_term(t->a->a, 0, t->b); again = 1; break; }
                Term *h = t; int n = 0; while (h->k == T_APP) { n++; h = h->a; }
                r = NULL;
                if (h->k == T_DATA) { r = global_level_at(datas[h->n].lvl, datas[h->n].poly, h); break; }
                if (h->k != T_DEF) break;
                Term *ty = defs[h->n].ty;
                for (int i = 0; i < n && ty && ty->k == T_PI; i++) ty = ty->b;
                if (!ty || ty->k != T_U) break;
                if (!ty->a) { r = lvl_const(ty->n); break; }
                if (ty->a->k == T_LVAL) { int hn, c; if (lv_is_hidden_plus(ty->a->lvl, &hn)) r = defs[h->n].poly ? lvl_suc(h->a ? h->a : lvl_const(0), hn) : lvl_const(hn); else if (lv_is_const(ty->a->lvl, &c)) r = lvl_const(c); }
                break; }
            default: r = NULL; break;
            }
        }
        if (!pushed) STACK_PUSH(&tlvst, Term *, r);
    }
    return STACK_POP(&tlvst, Term *);
}
/* print {name = level} when the level is known */

/* ---------------- terms ---------------- */

/* an element argument: a partial element standing here is on a face that holds (elab's silent coercion): applied to 1=1 */
static int is_partial_element(Term *t, int depth);
static void sp(void) { fputc(' ', out); }

/* a Glue system split into its types and its equivalences (Agda's record) */
static int sys_empty(Term *sys, int depth);
/* the partial element of a system: clauses on the faces' conjuncts; every face 0 dropped; a face 1 is a catch-all */
static int sys_empty(Term *sys, int depth) {
    for (int i = 0; i < sys->nbr; i++) { IVal f = face_iv(sys->br[i].face, depth); for (int c = 0; c < f.n; c++) if (conj_consistent(&f.c[c])) return 0; }
    return 1;
}

/* a spine: head and arguments in order */
static int spine(Term *t, Term ***argsp) {   /* the arguments of an application, on the heap (any number) */
    int n = 0; Term *w = t;
    while (w->k == T_APP) { n++; w = w->a; }
    Term **args = xalloc((n + 1) * sizeof(Term *));
    w = t; for (int i = n - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    *argsp = args; return n;
}
static Term *spine_head(Term *t) { while (t->k == T_APP) t = t->a; return t; }

static void binder_open(Term *t, int depth) {   /* NM(depth), KT(depth) for the binder of a T_PI / T_LAM / T_LET / T_SIGMA */
    NM(depth) = bind(depth, t->name);
    KT(depth).ty = t->k == T_PI || t->k == T_SIGMA ? t->a : t->k == T_LET ? t->a : NULL; KT(depth).depth = depth;
}
/* a cube constructor's method as written, \is -> inS t: the element t under the same lambdas (its type is the nested PathP) */
static Term *strip_ins(Term *m) {
    int n = 0; Term *w = m;
    while (w->k == T_LAM) { n++; w = w->a; }
    if (w->k != T_INS) return NULL;
    Term **ls = xalloc((n + 1) * sizeof(Term *)); w = m;
    for (int i = 0; i < n; i++) { ls[i] = w; w = w->a; }
    Term *b = w->a;
    for (int i = n - 1; i >= 0; i--) { Term *r = mk_lam(ls[i]->name, b, ls[i]->irr); r->isi = ls[i]->isi; r->imp = ls[i]->imp; b = r; }
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

/* a closed constructor spine of the BUILTIN NATURAL type prints as its literal (a normal form's suc^n zero) */
static int peano_literal(Term *t, unsigned long long *out_n) {
    unsigned long long n = 0; int zi, si;
    if (nat_builtin < 0 || !peano_shape(nat_builtin, &zi, &si)) return 0;
    while (t->k == T_APP && t->a->k == T_CON && t->a->n == si) { n++; t = t->b; }
    if (t->k == T_CON && t->n == zi) { *out_n = n; return 1; }
    if (t->k == T_NUM && t->n == nat_builtin && n) { char *s = bn_to_dec(t->num); unsigned long long v = strtoull(s, NULL, 10); free(s); if (v > (1ULL << 62)) return 0; *out_n = n + v; return 1; }
    return 0;
}
/* ---- the printer on the machine (machine.h) ----
   tp and the printers it calls are frames: printing, binder installation, and every look at the binders in scope (a type's
   level reads them) happen in the order the recursion took, with no C stack under them. */
typedef struct {
    MHdr h;
    Term *t; int depth, prec;
    Term *a, *b, *g, **args; const char *nm, *name;
    int n, i, c, nimp, lvl, nint, d2, paren, first, any; IVal f;
} AgF;
#define F ((AgF *)(mst.p + off))
static void tp_step(size_t off);
static void app_step(size_t off);
static void lam_step(size_t off);
static void lt_step(size_t off);
static void implicit_step(size_t off);
static void tp_arg_step(size_t off);
static void glue_T_step(size_t off);
static void equiv_rec_step(size_t off);
static void glue_e_step(size_t off);
static void sys_print_step(size_t off);
static AgF *apush(void (*step)(size_t), Term *t, int depth, int prec) { AgF *f = mpush(sizeof *f, step); f->t = t; f->depth = depth; f->prec = prec; return f; }
static void mpush_tp(Term *t, int depth, int prec) { apush(tp_step, t, depth, prec); }
static void mpush_tp_arg(Term *t, int depth) { apush(tp_arg_step, t, depth, 0); }
static void mpush_lt(Term *t, int depth, int prec) { apush(lt_step, t, depth, prec); }
static void mpush_implicit(const char *name, Term *l, int depth) { apush(implicit_step, l, depth, 0)->name = name; }
static void mpush_glue_T(Term *Te, int depth) { apush(glue_T_step, Te, depth, 0); }
static void mpush_equiv_rec(Term *e, int depth) { apush(equiv_rec_step, e, depth, 0); }
static void mpush_glue_e(Term *Te, int depth) { apush(glue_e_step, Te, depth, 0); }
static void mpush_sys_print(Term *sys, int depth) { apush(sys_print_step, sys, depth, 0); }

/* a level term */
static void lt_step(size_t off) {
    MSTART
    switch (F->t->k) {
    case T_LZERO: lv_const_print(F->t->n, F->prec); MRET(NULL);
    case T_LVAL: lv_print(F->t->lvl, F->depth, F->prec); MRET(NULL);
    case T_VAR: fputs(vname(F->depth, F->t->n), out); MRET(NULL);
    case T_LMETA: unsupported("level meta"); MRET(NULL);
    case T_LSUC: case T_LMAX: break;
    default: { Term *t = F->t; int d = F->depth, p = F->prec; MTAIL(mpush_tp(t, d, p)); }
    }
    if (F->t->k == T_LSUC) {
        if (F->t->n && F->prec > 0) fputc('(', out);
        for (int q = 0; q < F->t->n; q++) fputs("lsuc (", out);
        MCALL(mpush_lt(F->t->a, F->depth, 0));
        for (int q = 0; q < F->t->n; q++) fputc(')', out);
        if (F->t->n && F->prec > 0) fputc(')', out);
        MRET(NULL);
    }
    if (F->prec > 0) fputc('(', out);
    MCALL(mpush_lt(F->t->a, F->depth, 1)); fputs(" ⊔ ", out); MCALL(mpush_lt(F->t->b, F->depth, 1));
    if (F->prec > 0) fputc(')', out);
    MRET(NULL);
    MFINISH
}
/* print {name = level} when the level is known */
static void implicit_step(size_t off) {
    MSTART
    if (!F->t) MRET(NULL);
    fprintf(out, "{%s = ", F->name); MCALL(mpush_lt(F->t, F->depth, 0)); fputs("} ", out);
    MRET(NULL);
    MFINISH
}
/* an element argument: a partial element standing here is on a face that holds (elab's silent coercion): applied to 1=1 */
static void tp_arg_step(size_t off) {
    MSTART
    if (is_partial_element(F->t, F->depth)) { fputc('(', out); MCALL(mpush_tp(F->t, F->depth, 1)); fputs(" 1=1)", out); MRET(NULL); }
    { Term *t = F->t; int d = F->depth; MTAIL(mpush_tp(t, d, 2)); }
    MFINISH
}
/* a Glue system split into its types and its equivalences (Agda's record) */
static void glue_T_step(size_t off) {
    MSTART
    if (F->t->k != T_SYS) { fputs("(λ o → fst (", out); MCALL(mpush_tp(F->t, F->depth, 0)); fputs(" o))", out); MRET(NULL); }
    if (sys_empty(F->t, F->depth)) { fputs("(λ ())", out); MRET(NULL); }
    {   Term *Te = F->t; int d = F->depth;
        Term *s = mk_term(T_SYS, NULL, NULL, NULL, NULL); s->nbr = Te->nbr; s->br = xalloc((Te->nbr + 1) * sizeof(TBranch));
        for (int i = 0; i < Te->nbr; i++) { s->br[i].face = Te->br[i].face; s->br[i].body = Te->br[i].body->k == T_PAIR ? Te->br[i].body->a : mk_term(T_FST, Te->br[i].body, NULL, NULL, NULL); }
        MTAIL(mpush_sys_print(s, d)); }
    MFINISH
}
/* eezott's Equiv (f , p) as Agda's (f , record { equiv-proof = p }) */
static void equiv_rec_step(size_t off) {
    MSTART
    fputs("(", out);
    if (F->t->k == T_PAIR) { MCALL(mpush_tp(F->t->a, F->depth, 0)); fputs(" , record { equiv-proof = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0)); }
    else { fputs("fst ", out); MCALL(mpush_tp_arg(F->t, F->depth)); fputs(" , record { equiv-proof = snd ", out); MCALL(mpush_tp_arg(F->t, F->depth)); }
    fputs(" })", out);
    MRET(NULL);
    MFINISH
}
static void glue_e_step(size_t off) {
    MSTART
    if (F->t->k == T_SYS && sys_empty(F->t, F->depth)) { fputs("(λ ())", out); MRET(NULL); }
    if (F->t->k != T_SYS) {
        fputs("(λ o → (fst (snd (", out); MCALL(mpush_tp(F->t, F->depth, 0)); fputs(" o)) , record { equiv-proof = snd (snd (", out); MCALL(mpush_tp(F->t, F->depth, 0)); fputs(" o)) }))", out);
        MRET(NULL);
    }
    fputs("(λ { ", out); F->first = 1; F->any = 0;
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        F->f = face_iv(F->t->br[F->i].face, F->depth);
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            if (!F->first) fputs(" ; ", out);
            F->first = 0; F->any = 1;
            if (F->f.c[F->c].n == 0) fputs("_", out);
            for (int l = 0; l < F->f.c[F->c].n; l++) fprintf(out, "%s(%s = %s)", l ? " " : "", vname(F->depth, F->depth - 1 - F->f.c[F->c].l[l].var), F->f.c[F->c].l[l].neg ? "i0" : "i1");
            fputs(" → ", out);
            {   Term *b = F->t->br[F->i].body; F->a = b->k == T_PAIR ? b->b : mk_term(T_SND, b, NULL, NULL, NULL); }
            MCALL(mpush_equiv_rec(F->a, F->depth));
        }
    }
    if (!F->any) { fputs("})", out); MRET(NULL); }
    fputs(" })", out);
    MRET(NULL);
    MFINISH
}
/* the partial element of a system: clauses on the faces' conjuncts; every face 0 dropped; a face 1 is a catch-all */
static void sys_print_step(size_t off) {
    MSTART
    F->n = 0;
    for (int i = 0; i < F->t->nbr; i++) { IVal f = face_iv(F->t->br[i].face, F->depth); if (iv_is_one(f)) { F->n = i + 1; break; } }
    if (F->n) {
        fputs("(λ _ → ", out); F->a = F->t->br[F->n - 1].body; MCALL(mpush_tp(F->a, F->depth, 0));
        if (is_partial_element(F->a, F->depth)) fputs(" 1=1", out);
        fputc(')', out); MRET(NULL);
    }
    fputs("(λ { ", out); F->first = 1; F->any = 0;
    for (F->i = 0; F->i < F->t->nbr; F->i++) {
        F->f = face_iv(F->t->br[F->i].face, F->depth);
        for (F->c = 0; F->c < F->f.n; F->c++) {
            if (!conj_consistent(&F->f.c[F->c])) continue;
            if (!F->first) fputs(" ; ", out);
            F->first = 0; F->any = 1;
            for (int l = 0; l < F->f.c[F->c].n; l++) fprintf(out, "%s(%s = %s)", l ? " " : "", vname(F->depth, F->depth - 1 - F->f.c[F->c].l[l].var), F->f.c[F->c].l[l].neg ? "i0" : "i1");
            fputs(" → ", out);
            F->a = F->t->br[F->i].body; MCALL(mpush_tp(F->a, F->depth, 0));
            if (is_partial_element(F->a, F->depth)) fputs(" 1=1", out);
        }
    }
    if (!F->any) { fputs("())", out); MRET(NULL); }   /* never reached with a well-formed system: guarded by sys_empty */
    fputs(" })", out);
    MRET(NULL);
    MFINISH
}
static void lam_step(size_t off) {
    MSTART
    if (F->prec > 0) fputc('(', out);
    fputs("λ", out);
    {   Term *t = F->t; int depth = F->depth;
        while (t->k == T_LAM) {
            binder_open(t, depth);
            if ((t->irr & 2) && !strcmp(NM(depth), "_")) NM(depth) = bind(depth, "x");   /* an irrelevant binder needs a name: λ .x → */
            fprintf(out, " %s%s", (t->irr & 2) ? "." : "", NM(depth));
            depth++; t = t->a;
        }
        F->a = t; F->n = depth; }
    fputs(" → ", out); MCALL(mpush_tp(F->a, F->n, 0));
    if (F->prec > 0) fputc(')', out);
    MRET(NULL);
    MFINISH
}
static void app_step(size_t off) {
    MSTART
    if (F->t->k == T_APP && F->t->a->k == T_LAM) { Term *u = subst_term(F->t->a->a, 0, F->t->b); int d = F->depth, p = F->prec; MTAIL(mpush_tp(u, d, p)); }   /* a beta redex (comp's desugaring: (\i -> A) i1): Agda cannot sort an applied bare lambda */
    F->n = spine(F->t, &F->args);
    F->g = spine_head(F->t);
    F->nimp = 0; F->lvl = 0; F->nint = 0;   /* leading implicit arguments (a constructor's parameters), a level, missing intervals */
    if (F->g->k == T_CON) { Con *C = &cons[F->g->n]; Data *D = &datas[C->data]; F->nimp = D->nparams; F->lvl = D->poly; if (C->nint && F->n < F->nimp + C->nargs + C->nint) F->nint = F->nimp + C->nargs + C->nint - F->n; }
    if (F->nint && F->n < F->nimp + cons[F->g->n].nargs) { unsupported("a path constructor partially applied before its interval arguments"); F->nint = 0; }
    if (F->nint) for (int i = 0; i < F->n; i++) F->args[i] = shift(F->args[i], 0, F->nint);   /* the given arguments print under the interval lambdas (F4 found them unshifted) */
    {   Term *h = F->g;
        F->paren = F->nint || (F->prec > 1 && (F->n > 0 || F->lvl || (h->k == T_DEF && defs[h->n].poly) || (h->k == T_DATA && datas[h->n].poly) || (h->k == T_ELIM && datas[h->n].poly))); }
    if (F->paren) fputc('(', out);
    if (F->nint) { fputs("λ", out); for (int q = 0; q < F->nint; q++) { NM(F->depth + q) = bind(F->depth + q, xsprintf("ι%d", q)); fprintf(out, " %s", NM(F->depth + q)); } fputs(" → ", out); }
    F->d2 = F->depth + F->nint;
    /* the head, with its level (its first explicit argument) when it takes one */
    if (F->g->k == T_CON || F->g->k == T_DEF || F->g->k == T_DATA || F->g->k == T_ELIM) {
        int lv = F->g->k == T_CON ? F->lvl : F->g->k == T_DEF ? defs[F->g->n].poly : datas[F->g->n].poly;
        fputs(gname(F->g->k, F->g->n), out);
        if (lv) {
            fputs(F->g->k == T_CON ? " {" : " ", out);
            if (F->g->a) MCALL(mpush_lt(F->g->a, F->d2, 2)); else fputs("lzero", out);
            if (F->g->k == T_CON) fputc('}', out);
        }
    } else MCALL(mpush_tp(F->g, F->d2, 1));
    for (F->i = 0; F->i < F->n; F->i++) {
        if (F->i < F->nimp) { fputs(" {", out); MCALL(mpush_tp(F->args[F->i], F->d2, 0)); fputc('}', out); }
        else if (is_cube_method_arg(F->g, F->i)) {
            F->a = strip_ins(F->args[F->i]); sp();
            if (F->a) MCALL(mpush_tp_arg(F->a, F->d2)); else { unsupported("a cube method not of the form \\is -> inS t"); MCALL(mpush_tp_arg(F->args[F->i], F->d2)); }
        }
        else { sp(); MCALL(mpush_tp_arg(F->args[F->i], F->d2)); }
    }
    for (int q = 0; q < F->nint; q++) fprintf(out, " %s", NM(F->depth + q));
    if (F->paren) fputc(')', out);
    MRET(NULL);
    MFINISH
}
static void tp_step(size_t off) {
    MSTART
    if (!F->t) { fputs("?", out); MRET(NULL); }
    { unsigned long long n; if ((F->t->k == T_APP || F->t->k == T_CON) && peano_literal(F->t, &n)) { fprintf(out, "%llu", n); MRET(NULL); } }
    switch (F->t->k) {   /* the kinds that print nothing below them (no resume point inside this switch) */
    case T_VAR: fputs(vname(F->depth, F->t->n), out); MRET(NULL);
    case T_LEVEL: fputs("Level", out); MRET(NULL);
    case T_LZERO: case T_LSUC: case T_LMAX: case T_LVAL: { Term *t = F->t; int d = F->depth, p = F->prec; MTAIL(mpush_lt(t, d, p)); }
    case T_LMETA: unsupported("level meta"); MRET(NULL);
    case T_META: unsupported("unsolved meta ?%d", F->t->n); MRET(NULL);
    case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_APP: MBECOME(app_step);
    case T_NUM: {
        Term *t = F->t; int prec = F->prec;
        char *s = bn_to_dec(t->num);
        if (t->n == nat_builtin) fputs(s, out);
        else {
            unsigned long long v = strtoull(s, NULL, 10); int zi, si;
            if (strlen(s) > 4 || !peano_shape(t->n, &zi, &si)) unsupported("a literal %s of the data type %s, which is not the BUILTIN NATURAL", s, datas[t->n].name);
            else { if (prec > 1 && v) fputc('(', out); for (unsigned long long q = 0; q < v; q++) { fputs(gname(T_CON, si), out); sp(); } fputs(gname(T_CON, zi), out); if (prec > 1 && v) fputc(')', out); }
        }
        free(s); MRET(NULL); }
    case T_IRR: fputs("_", out); MRET(NULL);
    case T_INTERVAL: fputs("I", out); MRET(NULL);
    case T_I0: fputs("i0", out); MRET(NULL);
    case T_I1: fputs("i1", out); MRET(NULL);
    case T_LAM: MBECOME(lam_step);
    case T_SYS: if (sys_empty(F->t, F->depth)) { fputs("(λ ())", out); MRET(NULL); }   /* the absurd clause: IsOne i0 is empty (isOneEmpty's type would be unsolved) */
        { Term *t = F->t; int d = F->depth; MTAIL(mpush_sys_print(t, d)); }
    default: break;
    }
    #define PAREN_OPEN if (F->prec > 1) fputc('(', out)
    #define PAREN_CLOSE if (F->prec > 1) fputc(')', out)
    if (F->t->k == T_U) {
        PAREN_OPEN; fputs(F->t->pre ? "SSet " : "Set ", out);
        if (F->t->a) MCALL(mpush_lt(F->t->a, F->depth, 2)); else lv_const_print(F->t->n, 2);
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_INEG) { PAREN_OPEN; fputs("~ ", out); MCALL(mpush_tp(F->t->a, F->depth, 2)); PAREN_CLOSE; MRET(NULL); }
    if (F->t->k == T_IAND || F->t->k == T_IOR) {
        fputc('(', out); MCALL(mpush_tp(F->t->a, F->depth, 1)); fputs(F->t->k == T_IAND ? " ∧ " : " ∨ ", out); MCALL(mpush_tp(F->t->b, F->depth, 1)); fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PI) {
        if (F->prec > 0) fputc('(', out);
        F->c = term_mentions_var(F->t->b, 0);
        F->nm = (!F->t->name || !strcmp(F->t->name, "_")) ? (F->c ? bind(F->depth, "x") : "_") : bind(F->depth, F->t->name);
        if (!F->c && !strcmp(F->nm, "_")) { MCALL(mpush_tp(F->t->a, F->depth, 1)); fputs(" → ", out); }
        else {
            fprintf(out, "%s(%s : ", (F->t->irr & 2) ? "." : "", F->nm);
            if (F->t->isi || F->t->a->k == T_INTERVAL) fputs("I", out); else MCALL(mpush_tp(F->t->a, F->depth, 0));
            fputs(") → ", out);
        }
        NM(F->depth) = F->nm; KT(F->depth).ty = F->t->a; KT(F->depth).depth = F->depth;   /* after the domain: its binders live at this level too */
        MCALL(mpush_tp(F->t->b, F->depth + 1, 0));
        if (F->prec > 0) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_LET) {
        if (F->prec > 0) fputc('(', out);
        F->nm = bind(F->depth, F->t->name);
        fprintf(out, "let %s : ", F->nm); MCALL(mpush_tp(F->t->a, F->depth, 0)); fprintf(out, " ; %s = ", F->nm); MCALL(mpush_tp(F->t->b, F->depth, 0));
        NM(F->depth) = F->nm; KT(F->depth).ty = F->t->a; KT(F->depth).depth = F->depth;
        fputs(" in ", out); MCALL(mpush_tp(F->t->c, F->depth + 1, 0));
        if (F->prec > 0) fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_PATHP) {
        PAREN_OPEN; fputs("PathP ", out); MCALL(mpush_implicit("ℓ", type_level(F->t, F->depth), F->depth));
        MCALL(mpush_tp_arg(F->t->a, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->c, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_PAPP) { PAREN_OPEN; MCALL(mpush_tp(F->t->a, F->depth, 1)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth)); PAREN_CLOSE; MRET(NULL); }
    if (F->t->k == T_PARTIAL) { PAREN_OPEN; fputs("Partial ", out); MCALL(mpush_tp_arg(F->t->a, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth)); PAREN_CLOSE; MRET(NULL); }
    if (F->t->k == T_TRANSP) {
        PAREN_OPEN; fputs("transp ", out);
        F->a = F->t->a->k == T_LAM ? type_level(F->t->a->a, F->depth + 1) : NULL;   /* the line's level, constant along it */
        if (F->a && !term_mentions_var(F->a, 0)) { fputs("{ℓ = λ _ → ", out); MCALL(mpush_lt(shift(F->a, 0, -1), F->depth, 0)); fputs("} ", out); }
        MCALL(mpush_tp_arg(F->t->a, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->c, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_HCOMP) {
        PAREN_OPEN; fputs("hcomp ", out); MCALL(mpush_implicit("ℓ", type_level(F->t->a, F->depth), F->depth));
        fputs("{A = ", out); MCALL(mpush_tp(F->t->a, F->depth, 0)); fputs("} {φ = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0)); fputs("} ", out);
        MCALL(mpush_tp_arg(F->t->c, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->d, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_SUB) {
        PAREN_OPEN; fputs("Sub ", out); MCALL(mpush_tp_arg(F->t->a, F->depth)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth)); sp(); MCALL(mpush_tp(F->t->c, F->depth, 2));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_INS) { PAREN_OPEN; fputs("inS ", out); MCALL(mpush_tp_arg(F->t->a, F->depth)); PAREN_CLOSE; MRET(NULL); }
    if (F->t->k == T_OUTS) {
        {   Term *h = F->t->d; while (h->k == T_APP || h->k == T_PAPP) h = h->a;
            if (h->k == T_VAR) { int lvl = F->depth - 1 - h->n; Term *kt = (lvl >= 0 && lvl < F->depth) ? KT(lvl).ty : NULL;
                if (kt && kt->k == T_PATHP) { Term *u = F->t->d; int d = F->depth, p = F->prec; MTAIL(mpush_tp(u, d, p)); } } }   /* the element of a cube method: in Agda the method is the path itself */
        PAREN_OPEN;
        fputs("outS {A = ", out); MCALL(mpush_tp(F->t->a, F->depth, 0)); fputs("} {φ = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0));
        fputs("} {u = ", out); MCALL(mpush_tp(F->t->c, F->depth, 0)); fputs("} ", out); MCALL(mpush_tp_arg(F->t->d, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_SIGMA) {
        PAREN_OPEN; fputs(F->t->irr ? "Σᵢ " : "Σ ", out);
        F->a = type_level(F->t->a, F->depth); binder_open(F->t, F->depth); F->b = type_level(F->t->b, F->depth + 1);
        if (F->a && F->b) { MCALL(mpush_implicit("a", F->a, F->depth)); MCALL(mpush_implicit("b", F->b, F->depth + 1)); }
        MCALL(mpush_tp_arg(F->t->a, F->depth));
        binder_open(F->t, F->depth);
        if (!strcmp(NM(F->depth), "_")) NM(F->depth) = bind(F->depth, "x");
        fprintf(out, " (λ %s → ", NM(F->depth)); MCALL(mpush_tp(F->t->b, F->depth + 1, 0)); fputc(')', out);
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_PAIR) {   /* a lambda component parenthesized: its body would swallow the comma */
        fputc('(', out); MCALL(mpush_tp(F->t->a, F->depth, 1)); fputs((F->t->irr || F->t->n == 1) ? " ,ᵢ " : " , ", out); MCALL(mpush_tp(F->t->b, F->depth, 1)); fputc(')', out);
        MRET(NULL);
    }
    if (F->t->k == T_FST || F->t->k == T_SND) {
        PAREN_OPEN; fputs(F->t->k == T_FST ? ((F->t->irr || F->t->n == 1) ? "fstᵢ " : "fst ") : ((F->t->irr || F->t->n == 1) ? "sndᵢ " : "snd "), out);
        MCALL(mpush_tp_arg(F->t->a, F->depth)); PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_GLUE) {
        PAREN_OPEN; fputs("G.primGlue ", out);
        MCALL(mpush_implicit("ℓ", type_level(F->t->a, F->depth), F->depth)); MCALL(mpush_implicit("ℓ'", F->t->d ? F->t->d : lvl_const(F->t->n), F->depth));
        MCALL(mpush_tp_arg(F->t->a, F->depth)); fputs(" {φ = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0)); fputs("} ", out);
        MCALL(mpush_glue_T(F->t->c, F->depth)); sp(); MCALL(mpush_glue_e(F->t->c, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_GLUEEL) {
        F->g = F->t->c;
        PAREN_OPEN; fputs("G.prim^glue", out);
        if (F->g && F->g->k == T_GLUE) {
            sp(); MCALL(mpush_implicit("ℓ", type_level(F->g->a, F->depth), F->depth)); MCALL(mpush_implicit("ℓ'", F->g->d ? F->g->d : lvl_const(F->g->n), F->depth));
            fputs("{A = ", out); MCALL(mpush_tp(F->g->a, F->depth, 0)); fputs("} {φ = ", out); MCALL(mpush_tp(F->g->b, F->depth, 0));
            fputs("} {T = ", out); MCALL(mpush_glue_T(F->g->c, F->depth)); fputs("} {e = ", out); MCALL(mpush_glue_e(F->g->c, F->depth)); fputc('}', out);
        }
        sp(); MCALL(mpush_tp(F->t->a, F->depth, 2)); sp(); MCALL(mpush_tp_arg(F->t->b, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    if (F->t->k == T_UNGLUE) {
        PAREN_OPEN; fputs("G.prim^unglue ", out); MCALL(mpush_implicit("ℓ", type_level(F->t->b, F->depth), F->depth));
        fputs("{A = ", out); MCALL(mpush_tp(F->t->b, F->depth, 0)); fputs("} {φ = ", out); MCALL(mpush_tp(F->t->c, F->depth, 0));
        fputs("} {T = ", out); MCALL(mpush_glue_T(F->t->d, F->depth)); fputs("} {e = ", out); MCALL(mpush_glue_e(F->t->d, F->depth)); fputs("} ", out);
        MCALL(mpush_tp_arg(F->t->a, F->depth));
        PAREN_CLOSE; MRET(NULL);
    }
    #undef PAREN_OPEN
    #undef PAREN_CLOSE
    MRET(NULL);
    MFINISH
}
#undef F
/* the C entries (the declarations' printers call these; each runs the machine to the end of its term) */
static void tp(Term *t, int depth, int prec) { mpush_tp(t, depth, prec); mrun(); }
static void tp_arg(Term *t, int depth) { mpush_tp_arg(t, depth); mrun(); }
static void implicit_level(const char *name, Term *l, int depth) { mpush_implicit(name, l, depth); mrun(); }

/* ---------------- declarations ---------------- */

static void level_binder(int depth, const char *nm, int explicit_) {
    NM(depth) = nm; KT(depth).ty = NULL;
    fprintf(out, explicit_ ? "(%s : Level) → " : "{%s : Level} → ", nm);
}

/* F2a, tried and withdrawn: printing the natives add/mul in Agda's BUILTIN NATPLUS/NATTIMES clause shape makes Agda compute
   literals natively, but it changes definitional equality on open terms: in eezott  add k b  unfolds to its elim body, which
   the prelude's laws rely on (add k b = elim Nat (\_ -> Nat) b (\k ih -> suc ih) k by refl); Agda's clause-defined add is stuck
   on a variable k. The natives print as their bodies; big literals are the run-time leg's business (RESOURCE in Agda). */
/* a definition: its type, then its value with the leading lambdas typed by the telescope */
static void print_def(int i) {
    Def *D = &defs[i];
    const char *nm = gname(T_DEF, i);
    ownlvl = D->poly ? "ℓ" : NULL;
    int depth = 0;
    fprintf(out, "%s : ", nm);
    if (D->poly) level_binder(depth++, "ℓ", 1);
    tp(D->ty, depth, 0);
    fprintf(out, "\n%s", nm);
    if (D->poly) fputs(" ℓ", out);
    /* the leading lambdas as clause variables, typed by the Pi telescope */
    Term *ty = D->ty, *v = D->val;
    while (v->k == T_LAM && ty->k == T_PI) {
        binder_open(v, depth); KT(depth).ty = ty->a; KT(depth).depth = depth;
        fprintf(out, " %s", NM(depth));   /* a clause variable: irrelevance comes from the signature (a dot here would be an inaccessible pattern) */
        depth++; v = v->a; ty = ty->b;
    }
    fputs(" = ", out); tp(v, depth, 0); fputs("\n\n", out);
    ownlvl = NULL;
}

/* the parameters of a data type as binders (names p0.., typed) */
static void data_params(Data *D, int depth0) {
    for (int i = 0; i < D->nparams; i++) {
        const char *nm = bind(depth0 + i, xsprintf("p%d", i));
        fprintf(out, " (%s : ", nm); tp(D->ptys[i], depth0 + i, 0); fputc(')', out);
        NM(depth0 + i) = nm; KT(depth0 + i).ty = D->ptys[i]; KT(depth0 + i).depth = depth0 + i;
    }
}
/* data D (ℓd)? (params) : (indices) → Set lvl */
static void data_sig(int d, int with_where) {
    Data *D = &datas[d];
    ownlvl = D->poly ? "ℓd" : NULL;
    int depth = 0;
    fprintf(out, "data %s", gname(T_DATA, d));
    if (D->poly) { NM(depth) = "ℓd"; KT(depth).ty = NULL; fputs(" (ℓd : Level)", out); depth++; }
    data_params(D, depth); depth += D->nparams;
    fputs(" : ", out);
    for (int j = 0; j < D->nidx; j++) {
        const char *nm = bind(depth, xsprintf("i%d", j));
        fprintf(out, "(%s : ", nm); tp(D->itys[j], depth, 0); fputs(") → ", out);
        NM(depth) = nm; KT(depth).ty = D->itys[j]; KT(depth).depth = depth; depth++;
    }
    fputs("Set ", out); lv_print(D->lvl, depth, 2);
    fputs(with_where ? " where\n" : "\n", out);
}
/* the constructors of D (under 'data D where' or the combined declaration) */
static void data_cons(int d) {
    Data *D = &datas[d];
    ownlvl = D->poly ? "ℓd" : NULL;
    int depth = 0;
    if (D->poly) { NM(depth++) = "ℓd"; }
    for (int i = 0; i < D->nparams; i++) { NM(depth) = bind(depth, xsprintf("p%d", i)); KT(depth).ty = D->ptys[i]; KT(depth).depth = depth; depth++; }
    int np = depth;
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fprintf(out, "  %s : ", gname(T_CON, D->cons[ci]));
        int dep = np;
        for (int j = 0; j < C->nargs; j++) {
            ConArg *A = &C->args[j];
            const char *nm = bind(dep, A->name);
            if (!strcmp(nm, "_")) { tp(A->ty, dep, 1); fputs(" → ", out); }
            else { fprintf(out, "%s(%s : ", (A->irr & 2) ? "." : "", nm); tp(A->ty, dep, 0); fputs(") → ", out); }
            NM(dep) = nm; KT(dep).ty = A->ty; KT(dep).depth = dep;
            dep++;
        }
        /* the result: D ℓd? p.. ridx.., under [params, args, intervals] (the return indices are read at that depth, elab
           data_spine); a path constructor: the nested PathP of its boundary */
        int n = C->nint;
        Term *res = mk_ref(T_DATA, d);
        if (D->poly) res->a = mk_lval(lv_hidden());
        for (int i = 0; i < D->nparams; i++) res = mk_app(res, mk_var(dep + n - 1 - (D->poly ? 1 : 0) - i), 1);
        for (int j = 0; j < D->nidx; j++) res = mk_app(res, C->ridx[j], 1);
        if (n == 0) tp(res, dep, 0);
        else if (!C->boundary) unsupported("constructor %s has interval binders but no boundary", C->name);
        else {
            for (int q = 0; q < n; q++) { NM(dep + q) = bind(dep + q, xsprintf("i%d", q)); KT(dep + q).ty = NULL; }
            Term *c = cube(res, C->boundary->br, C->boundary->nbr, n, dep + n);
            if (!c) unsupported("constructor %s: its boundary is not a full cube", C->name);
            else tp(c, dep, 0);
        }
        fputc('\n', out);
    }
}

/* the eliminator of D: its type is eezott's (elim_type, cube methods as nested PathP), its clauses one per constructor */
static void print_elim(int d, int what) {   /* what: 1 signature, 2 clauses, 3 both */
    Data *D = &datas[d];
    int np = D->nparams, nbk = D->nblock, K = block_ncons(d), m = D->nidx;
    const char *en = gname(T_ELIM, d);
    ownlvl = NULL;
    int depth = 0;
    if (what & 1) {
    fprintf(out, "%s : ", en);
    level_binder(depth++, "ℓ", 0);
    LVal dl = lv_const(0);
    if (D->poly) { level_binder(depth++, "ℓd", 1); dl = lv_var(1); }
    Term *ety = elim_type(d, lv_var(0), 0, dl);
    /* walk the Pi chain: parameters explicit, methods rewritten */
    Term *w = ety; int nbind = 0;
    while (w->k == T_PI) {
        Term *dom = w->a;
        if (w->name && !strncmp(w->name, "m_", 2)) dom = fix_method(dom, depth);
        const char *nm = (!w->name || !strcmp(w->name, "_")) ? bind(depth, "x") : bind(depth, w->name);
        fprintf(out, "%s(%s : ", (w->irr & 2) ? "." : "", nm);
        if (w->isi || dom->k == T_INTERVAL) fputs("I", out); else tp(dom, depth, 0);
        fputs(") → ", out);
        NM(depth) = nm; KT(depth).ty = dom; KT(depth).depth = depth;
        depth++; nbind++; w = w->b;
    }
    tp(w, depth, 0); fputc('\n', out);
    }
    if (!(what & 2)) { fputc('\n', out); return; }
    /* clauses: elim ℓd? p.. P.. m.. i.. (c a.. is..) = m_c a.. ih.. is.. */
    const char **pn = xalloc((np + 1) * sizeof(char *)), **Pn = xalloc((nbk + 1) * sizeof(char *)), **mn = xalloc((K + 1) * sizeof(char *));
    if (D->ncons == 0) {   /* no constructors: the absurd clause */
        fputs(en, out); if (D->poly) fputs(" _", out);
        for (int i = 0; i < np + nbk + K + m; i++) fputs(" _", out);
        fputs(" ()\n\n", out); return;
    }
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]]; int r = C->nargs;
        int dep = 0;
        fprintf(out, "%s {ℓ}", en);   /* the motive's level, bound here and passed to the recursive calls: cumulativity leaves it unsolved otherwise */
        if (D->poly) { NM(dep) = "ℓd"; KT(dep).ty = NULL; fputs(" ℓd", out); dep++; }
        for (int i = 0; i < np; i++) { pn[i] = NM(dep) = bind(dep, xsprintf("p%d", i)); KT(dep).ty = D->ptys[i]; KT(dep).depth = dep; fprintf(out, " %s", pn[i]); dep++; }
        int pdep = dep;   /* [ℓd?, params] */
        for (int i = 0; i < nbk; i++) { Pn[i] = NM(dep) = bind(dep, xsprintf("P%d", i)); KT(dep).ty = NULL; fprintf(out, " %s", Pn[i]); dep++; }
        for (int i = 0; i < K; i++) { mn[i] = NM(dep) = bind(dep, xsprintf("m%d", i)); KT(dep).ty = NULL; fprintf(out, " %s", mn[i]); dep++; }
        for (int j = 0; j < m; j++) fputs(" _", out);
        /* the constructor pattern: its arguments are named at levels pdep.. so that index terms print under [params, args] */
        fprintf(out, " (%s", gname(T_CON, D->cons[ci]));
        const char **an = xalloc((r + 1) * sizeof(char *));
        for (int j = 0; j < r; j++) { an[j] = NM(pdep + j) = bind(pdep + j, C->args[j].name && strcmp(C->args[j].name, "_") ? C->args[j].name : xsprintf("a%d", j)); KT(pdep + j).ty = C->args[j].ty; KT(pdep + j).depth = pdep + j; fprintf(out, " %s", an[j]); }
        const char **in = xalloc((C->nint + 1) * sizeof(char *));
        for (int q = 0; q < C->nint; q++) { in[q] = NM(pdep + r + q) = bind(pdep + r + q, xsprintf("j%d", q)); fprintf(out, " %s", in[q]); }
        fprintf(out, ") = %s", mn[C->bord]);
        for (int j = 0; j < r; j++) fprintf(out, " %s", an[j]);
        /* induction hypotheses, in argument order */
        for (int j = 0; j < r; j++) {
            ConArg *A = &C->args[j];
            if (!A->isrec && !A->isrecpath) continue;
            int rm = A->rec; Data *RM = &datas[rm];
            int q = A->isrecpath ? 1 : A->npi;
            int ydep = pdep + j;   /* the y binders live above [params, a_0..a_{j-1}] */
            fputs(q ? " (λ" : " (", out);
            for (int y = 0; y < q; y++) { NM(ydep + y) = bind(ydep + y, A->isrecpath ? "k" : xsprintf("y%d", y)); KT(ydep + y).ty = NULL; fprintf(out, " %s", NM(ydep + y)); }
            fprintf(out, q ? " → %s {ℓ}" : "%s {ℓ}", gname(T_ELIM, rm));
            if (RM->poly) fputs(" ℓd", out);
            for (int i = 0; i < np; i++) fprintf(out, " %s", pn[i]);
            for (int i = 0; i < nbk; i++) fprintf(out, " %s", Pn[i]);
            for (int i = 0; i < K; i++) fprintf(out, " %s", mn[i]);
            if (!A->isrecpath) for (int i = 0; i < A->nidx; i++) { sp(); tp_arg(A->idx[i], ydep + q); }
            if (q) { fprintf(out, " (%s", an[j]); for (int y = 0; y < q; y++) fprintf(out, " %s", NM(ydep + y)); fputs("))", out); }
            else fprintf(out, " %s)", an[j]);
            /* restore the argument names shadowed by the y binders */
            for (int y = 0; y < q && j + y < r; y++) NM(pdep + j + y) = an[j + y];
            for (int y = 0; y < q; y++) if (j + y >= r && j + y < r + C->nint) NM(pdep + j + y) = in[j + y - r];
        }
        for (int q = 0; q < C->nint; q++) fprintf(out, " %s", in[q]);
        fputc('\n', out);
    }
    fputc('\n', out);
}

static void header(const char *modname) {
    fprintf(out, "{-# OPTIONS --cubical --cumulativity #-}\n");   /* eezott's universes are cumulative (check: U l <= U l'); Agda's only with the flag */
    fprintf(out, "-- generated by eezott -A: the elaborated program, for Agda's --cubical mode as the differential oracle (M20)\n");
    fprintf(out, "module %s where\n", modname);
    fputs("open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)\n", out);
    fputs("open import Agda.Primitive.Cubical using (I ; i0 ; i1 ; IsOne ; Partial ; PartialP ; isOneEmpty) renaming (primIMin to _∧_ ; primIMax to _∨_ ; primINeg to ~_ ; primTransp to transp ; primHComp to hcomp ; itIsOne to 1=1)\n", out);
    fputs("open import Agda.Builtin.Cubical.Path using (PathP)\n", out);
    fputs("open import Agda.Builtin.Cubical.Sub using (Sub ; inS) renaming (primSubOut to outS)\n", out);
    fputs("import Agda.Builtin.Cubical.Glue as G\n", out);
    fputs("open import Agda.Builtin.Sigma using (Σ ; _,_ ; fst ; snd)\n", out);
    fputs("\n-- a Sigma whose second component is irrelevant (eezott's Sigma A .B)\n", out);
    fputs("record Σᵢ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where\n  constructor _,ᵢ_\n  field\n    fstᵢ : A\n    .sndᵢ : B fstᵢ\nopen Σᵢ public\ninfixr 4 _,ᵢ_\n\n", out);
}

typedef struct { int seq, isdata, id; } Decl;
static int decl_cmp(const void *a, const void *b) { return ((const Decl *)a)->seq - ((const Decl *)b)->seq; }

/* ---- reachability: only what the program's own declarations use is printed (the preludes are large; a definition the
   program never touches that Agda cannot say must not hide the program) ---- */
static Stack needst = { NULL, 0, 0, sizeof(Term *) };
static void need_push(Term *t) { if (t) STACK_PUSH(&needst, Term *, t); }
static void need_data_mark(int d) {
    Data *D = &datas[d]; if (needdata[d]) return;
    for (int k = 0; k < D->nblock; k++) {   /* a block is printed whole */
        int m = D->block + k; if (needdata[m]) continue; needdata[m] = 1;
        Data *M = &datas[m];
        for (int i = 0; i < M->nparams; i++) need_push(M->ptys[i]);
        for (int j = 0; j < M->nidx; j++) need_push(M->itys[j]);
        for (int ci = 0; ci < M->ncons; ci++) {
            Con *C = &cons[M->cons[ci]];
            for (int j = 0; j < C->nargs; j++) need_push(C->args[j].ty);
            for (int j = 0; j < M->nidx; j++) need_push(C->ridx[j]);
            if (C->boundary) need_push(C->boundary);
        }
    }
}
static void need_def_mark(int i) { if (needdef[i]) return; needdef[i] = 1; need_push(defs[i].ty); need_push(defs[i].val); }
static void need_run(void) {   /* marking: the order does not matter */
    while (needst.n) {
        Term *t = STACK_POP(&needst, Term *);
        switch (t->k) {
        case T_DEF: need_def_mark(t->n); need_push(t->a); break;
        case T_DATA: case T_ELIM: need_data_mark(t->n); need_push(t->a); break;
        case T_CON: need_data_mark(cons[t->n].data); need_push(t->a); break;
        case T_NUM: need_data_mark(t->n); need_push(t->a); break;
        case T_SYS: for (int i = 0; i < t->nbr; i++) { need_push(t->br[i].face); need_push(t->br[i].body); } break;
        default: need_push(t->a); need_push(t->b); need_push(t->c); need_push(t->d); break;
        }
    }
}
static void need_def(int i) { need_def_mark(i); need_run(); }
static void need_data(int d) { need_data_mark(d); need_run(); }

int agda_program(FILE *f, const char *modname, int first_seq, const char *nfname) {
    out = f; nunsup = 0;
    needdef = xalloc(ndefs + 1); needdata = xalloc(ndatas + 1);
    for (int i = 0; i < ndefs; i++) if (defs[i].seq >= first_seq) need_def(i);
    for (int d = 0; d < ndatas; d++) if (datas[d].seq >= first_seq) need_data(d);
    header(modname);
    Decl *ds = xalloc((ndefs + ndatas + 1) * sizeof(Decl)); int nd = 0;
    for (int i = 0; i < ndefs; i++) if (needdef[i]) ds[nd++] = (Decl){ defs[i].seq, 0, i };
    for (int d = 0; d < ndatas; d++) if (needdata[d] && datas[d].bpos == 0) ds[nd++] = (Decl){ datas[d].seq, 1, d };   /* a block at its first member */
    qsort(ds, nd, sizeof(Decl), decl_cmp);
    for (int i = 0; i < ndatas; i++) { int zi, si; if (nat_builtin < 0 && peano_shape(i, &zi, &si)) nat_builtin = i; }
    for (int i = 0; i < nd; i++) {
        if (!ds[i].isdata) { print_def(ds[i].id); continue; }
        int d = ds[i].id; Data *D = &datas[d];
        if (D->nblock == 1) { data_sig(d, 1); data_cons(d); fputc('\n', out); }
        else {
            for (int k = 0; k < D->nblock; k++) data_sig(D->block + k, 0);
            for (int k = 0; k < D->nblock; k++) { fprintf(out, "data %s where\n", gname(T_DATA, D->block + k)); data_cons(D->block + k); }
            fputc('\n', out);
        }
        if (d == nat_builtin) fprintf(out, "{-# BUILTIN NATURAL %s #-}\n\n", gname(T_DATA, d));
        if (D->nblock == 1) print_elim(d, 3);
        else { for (int k = 0; k < D->nblock; k++) print_elim(D->block + k, 1); for (int k = 0; k < D->nblock; k++) print_elim(D->block + k, 2); }
    }
    /* F2b: the checker's normal form of the definition named by -n (the program's main, in the harness), for Agda to judge:
       nf_d : PathP (\_ -> T) d nf ; nf_d = \_ -> nf  holds iff Agda finds d and nf convertible. Only on request: a normal
       form may be unholdable (the literal-elimination tripwire, exit 70), which the harness then records, not the printer */
    if (nfname) for (int i = 0; i < nd; i++) {
        if (ds[i].isdata) continue;
        int id = ds[i].id; Def *D = &defs[id];
        if (strcmp(D->name, nfname) || D->poly) continue;
        Val *ty = force(D->vty); if (ty->k != V_DATA) continue;
        Term *nf0 = quote(0, nf_force(D->vval));
        { unsigned long long n; int big = 0;   /* a literal beyond Agda's unary reach: no equation (the run-time leg observes the value) */
          if (nf0->k == T_NUM) { char *dec = bn_to_dec(nf0->num); big = strlen(dec) > 5; free(dec); }
          else if ((nf0->k == T_APP || nf0->k == T_CON) && peano_literal(nf0, &n)) big = n > 100000;
          if (big) { fprintf(out, "-- the normal form of %s is a literal Agda would evaluate in unary: no equation; the run-time leg observes it\n", D->name); continue; } }
        fputs("-- the checker's normal form (eezott -n), a definitional equation for Agda to check\n", out);
        Term *T = quote(0, ty), *nf = nf0;
        const char *nm = gname(T_DEF, id);
        ownlvl = NULL;
        fprintf(out, "nfˍ%s : PathP ", nm); implicit_level("ℓ", type_level(T, 0), 0); fputs("(λ _ → ", out); tp(T, 0, 0); fputs(") ", out); fputs(nm, out); sp(); tp_arg(nf, 0);
        fprintf(out, "\nnfˍ%s = λ _ → ", nm); tp(nf, 0, 0); fputs("\n\n", out);
    }
    if (nunsup) fprintf(out, "-- %d unsupported construct%s: this module is not a faithful image of the program\n", nunsup, nunsup == 1 ? "" : "s");
    return nunsup ? 3 : 0;
}
