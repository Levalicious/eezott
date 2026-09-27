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

static FILE *out;
static int nunsup;
static const char *ownlvl;          /* the name of the hidden level of the global being printed (NULL: none) */
static int nat_builtin = -1;        /* the data type declared BUILTIN NATURAL (the first shaped like the naturals) */

/* a binder's known type: the term and the depth it lives at (for the 1=1 coercion) */
typedef struct { Term *ty; int depth; } KTy;
static KTy ktys[4096];
static const char *names[4096];

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
        for (int i = 0; i < depth && !clash; i++) if (names[i] && !strcmp(names[i], r)) clash = 1;
        if (!clash) return r;
        r = xsprintf("%s′", r);
    }
}
static const char *vname(int depth, int idx) {
    int lvl = depth - 1 - idx;
    if (lvl >= 0 && lvl < depth && names[lvl]) return names[lvl];
    return xsprintf("#%d", idx);
}

/* ---------------- levels ---------------- */

static void tp(Term *t, int depth, int prec);
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
static void lt_print(Term *t, int depth, int prec) {
    switch (t->k) {
    case T_LZERO: lv_const_print(t->n, prec); break;
    case T_LVAL: lv_print(t->lvl, depth, prec); break;
    case T_VAR: fputs(vname(depth, t->n), out); break;
    case T_LSUC:
        if (t->n && prec > 0) fputc('(', out);
        for (int q = 0; q < t->n; q++) fputs("lsuc (", out);
        lt_print(t->a, depth, 0);
        for (int q = 0; q < t->n; q++) fputc(')', out);
        if (t->n && prec > 0) fputc(')', out);
        break;
    case T_LMAX: if (prec > 0) fputc('(', out); lt_print(t->a, depth, 1); fputs(" ⊔ ", out); lt_print(t->b, depth, 1); if (prec > 0) fputc(')', out); break;
    case T_LMETA: unsupported("level meta"); break;
    default: tp(t, depth, prec); break;
    }
}
/* the level a polymorphic global reference is taken at (its first explicit argument) */
static void ref_level(Term *t, int depth) {
    if (t->a) lt_print(t->a, depth, 2); else fputs("lzero", out);
}

/* ---------------- the interval and faces ---------------- */

/* a face term to the free De Morgan algebra (variables by level) */
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
/* the clauses of a partial element: one per consistent conjunct of each branch's face */
static void sys_print(Term *sys, int depth);
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
    if (t->k == T_VAR) { int lvl = depth - 1 - t->n; return (lvl >= 0 && lvl < depth) ? ktys[lvl].ty : NULL; }
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
    if (n == 0) return ty;
    int v = n - 1;   /* i_0 */
    Term *b0 = branch_at(br, nbr, v, 0, depth), *b1 = branch_at(br, nbr, v, 1, depth);
    if (!b0 || !b1) return NULL;
    Term *inner = cube(ty, br, nbr, n - 1, depth);
    if (!inner) return NULL;
    Term *line = mk_lam("i", inner, 0); line->isi = 1;
    Term *e0 = subst_term(b0, v, mk_term(T_I0, NULL, NULL, NULL, NULL)), *e1 = subst_term(b1, v, mk_term(T_I1, NULL, NULL, NULL, NULL));
    for (int q = n - 2; q >= 0; q--) { e0 = mk_lam("j", e0, 0); e0->isi = 1; e1 = mk_lam("j", e1, 0); e1->isi = 1; }
    return mk_term(T_PATHP, line, e0, e1, NULL);
}
/* a method's type from elim_type, its cube form (is : I) -> Sub (P (c a is)) phi [faces -> E(boundary)] rewritten as the
   nested PathP; other shapes returned as they are */
static Term *fix_method(Term *mt, int depth) {
    if (mt->k == T_PI && !(mt->isi || mt->a->k == T_INTERVAL)) {
        Term *r = mk_pi(mt->name, mt->a, fix_method(mt->b, depth + 1), mt->irr); r->imp = mt->imp; r->isi = mt->isi; r->pre = mt->pre; return r;
    }
    int n = 0; Term *w = mt;
    while (w->k == T_PI && (w->isi || w->a->k == T_INTERVAL)) { n++; w = w->b; }
    if (n == 0) return mt;
    if (w->k == T_SUB && w->c->k == T_SYS) {
        Term *c = cube(w->a, w->c->br, w->c->nbr, n, depth + n);
        if (c) return c;
        unsupported("a cube method whose boundary is not a full cube"); return mt;
    }
    if (w->k == T_PATHP) return mt;
    unsupported("an interval-binder method without a boundary"); return mt;
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
static Term *type_level(Term *t, int depth) {
    if (!t) return NULL;
    switch (t->k) {
    case T_U: return u_level(t);
    case T_PI: if (t->isi || t->a->k == T_INTERVAL || t->a->k == T_LEVEL) return type_level(t->b, depth + 1); return lvl_max(type_level(t->a, depth), type_level(t->b, depth + 1));
    case T_SIGMA: return lvl_max(type_level(t->a, depth), type_level(t->b, depth + 1));
    case T_PATHP: return t->a->k == T_LAM ? type_level(t->a->a, depth + 1) : NULL;
    case T_PARTIAL: return type_level(t->b, depth);
    case T_SUB: return type_level(t->a, depth);
    case T_GLUE: return t->d ? t->d : lvl_const(t->n);
    case T_VAR: { int lvl = depth - 1 - t->n; Term *kt = (lvl >= 0 && lvl < depth) ? ktys[lvl].ty : NULL;
        if (kt && kt->k == T_U) { if (!kt->a) return lvl_const(kt->n); if (kt->a->k == T_LVAL || kt->a->k == T_LZERO) return kt->a; }
        return NULL; }
    case T_DATA: return global_level_at(datas[t->n].lvl, datas[t->n].poly, t);
    case T_APP: case T_DEF: {
        if (t->k == T_APP && t->a->k == T_LAM) return type_level(subst_term(t->a->a, 0, t->b), depth);
        Term *h = t; int n = 0; while (h->k == T_APP) { n++; h = h->a; }
        if (h->k == T_DATA) return global_level_at(datas[h->n].lvl, datas[h->n].poly, h);
        if (h->k != T_DEF) return NULL;
        Term *ty = defs[h->n].ty;
        for (int i = 0; i < n && ty && ty->k == T_PI; i++) ty = ty->b;
        if (!ty || ty->k != T_U) return NULL;
        if (!ty->a) return lvl_const(ty->n);
        if (ty->a->k == T_LVAL) { int hn, c; if (lv_is_hidden_plus(ty->a->lvl, &hn)) return defs[h->n].poly ? lvl_suc(h->a ? h->a : lvl_const(0), hn) : lvl_const(hn); if (lv_is_const(ty->a->lvl, &c)) return lvl_const(c); }
        return NULL; }
    default: return NULL;
    }
}
/* print {name = level} when the level is known */
static void implicit_level(const char *name, Term *l, int depth) {
    if (!l) return;
    fprintf(out, "{%s = ", name); lt_print(l, depth, 0); fputs("} ", out);
}

/* ---------------- terms ---------------- */

/* an element argument: a partial element standing here is on a face that holds (elab's silent coercion): applied to 1=1 */
static int is_partial_element(Term *t, int depth);
static void tp_arg(Term *t, int depth) {
    if (is_partial_element(t, depth)) { fputc('(', out); tp(t, depth, 1); fputs(" 1=1)", out); }
    else tp(t, depth, 2);
}
static void tp_parg(Term *t, int depth) { tp(t, depth, 2); }   /* a position that takes a partial element */
static void sp(void) { fputc(' ', out); }

/* a Glue system split into its types and its equivalences (Agda's record) */
static void glue_T(Term *Te, int depth) {
    if (Te->k != T_SYS) { fputs("(λ o → fst (", out); tp(Te, depth, 0); fputs(" o))", out); return; }
    Term *s = mk_term(T_SYS, NULL, NULL, NULL, NULL); s->nbr = Te->nbr; s->br = xalloc((Te->nbr + 1) * sizeof(TBranch));
    for (int i = 0; i < Te->nbr; i++) { s->br[i].face = Te->br[i].face; s->br[i].body = Te->br[i].body->k == T_PAIR ? Te->br[i].body->a : mk_term(T_FST, Te->br[i].body, NULL, NULL, NULL); }
    sys_print(s, depth);
}
static void equiv_rec(Term *e, int depth) {   /* eezott's Equiv (f , p) as Agda's (f , record { equiv-proof = p }) */
    fputs("(", out);
    if (e->k == T_PAIR) { tp(e->a, depth, 0); fputs(" , record { equiv-proof = ", out); tp(e->b, depth, 0); }
    else { fputs("fst ", out); tp_arg(e, depth); fputs(" , record { equiv-proof = snd ", out); tp_arg(e, depth); }
    fputs(" })", out);
}
static void glue_e(Term *Te, int depth) {
    if (Te->k != T_SYS) {
        fputs("(λ o → (fst (snd (", out); tp(Te, depth, 0); fputs(" o)) , record { equiv-proof = snd (snd (", out); tp(Te, depth, 0); fputs(" o)) }))", out); return;
    }
    fputs("(λ { ", out); int first = 1, any = 0;
    for (int i = 0; i < Te->nbr; i++) {
        IVal f = face_iv(Te->br[i].face, depth);
        for (int c = 0; c < f.n; c++) {
            if (!conj_consistent(&f.c[c])) continue;
            if (!first) fputs(" ; ", out);
            first = 0; any = 1;
            if (f.c[c].n == 0) fputs("_", out);
            for (int l = 0; l < f.c[c].n; l++) fprintf(out, "%s(%s = %s)", l ? " " : "", vname(depth, depth - 1 - f.c[c].l[l].var), f.c[c].l[l].neg ? "i0" : "i1");
            fputs(" → ", out);
            Term *b = Te->br[i].body;
            equiv_rec(b->k == T_PAIR ? b->b : mk_term(T_SND, b, NULL, NULL, NULL), depth);
        }
    }
    if (!any) { fputs("})", out); return; }
    fputs(" })", out);
}
/* the partial element of a system: clauses on the faces' conjuncts; every face 0 dropped; a face 1 is a catch-all */
static void sys_print(Term *sys, int depth) {
    int total = 0;
    for (int i = 0; i < sys->nbr; i++) { IVal f = face_iv(sys->br[i].face, depth); if (iv_is_one(f)) { total = i + 1; break; } }
    if (total) { fputs("(λ _ → ", out); Term *b = sys->br[total - 1].body; tp(b, depth, 0); if (is_partial_element(b, depth)) fputs(" 1=1", out); fputc(')', out); return; }
    fputs("(λ { ", out); int first = 1, any = 0;
    for (int i = 0; i < sys->nbr; i++) {
        IVal f = face_iv(sys->br[i].face, depth);
        for (int c = 0; c < f.n; c++) {
            if (!conj_consistent(&f.c[c])) continue;
            if (!first) fputs(" ; ", out);
            first = 0; any = 1;
            for (int l = 0; l < f.c[c].n; l++) fprintf(out, "%s(%s = %s)", l ? " " : "", vname(depth, depth - 1 - f.c[c].l[l].var), f.c[c].l[l].neg ? "i0" : "i1");
            fputs(" → ", out);
            Term *b = sys->br[i].body; tp(b, depth, 0);
            if (is_partial_element(b, depth)) fputs(" 1=1", out);
        }
    }
    if (!any) { fputs("())", out); return; }   /* never reached with a well-formed system: guarded by sys_empty */
    fputs(" })", out);
}
static int sys_empty(Term *sys, int depth) {
    for (int i = 0; i < sys->nbr; i++) { IVal f = face_iv(sys->br[i].face, depth); for (int c = 0; c < f.n; c++) if (conj_consistent(&f.c[c])) return 0; }
    return 1;
}

/* a spine: head and arguments in order */
static int spine(Term *t, Term **args, int max) {
    int n = 0; Term *w = t;
    while (w->k == T_APP) { n++; w = w->a; }
    if (n > max) return -1;
    w = t; for (int i = n - 1; i >= 0; i--) { args[i] = w->b; w = w->a; }
    return n;
}
static Term *spine_head(Term *t) { while (t->k == T_APP) t = t->a; return t; }

static void binder_open(Term *t, int depth) {   /* names[depth], ktys[depth] for the binder of a T_PI / T_LAM / T_LET / T_SIGMA */
    names[depth] = bind(depth, t->name);
    ktys[depth].ty = t->k == T_PI || t->k == T_SIGMA ? t->a : t->k == T_LET ? t->a : NULL; ktys[depth].depth = depth;
}
static void lam_print(Term *t, int depth, int prec) {
    if (prec > 0) fputc('(', out);
    fputs("λ", out);
    while (t->k == T_LAM) {
        binder_open(t, depth);
        if ((t->irr & 2) && !strcmp(names[depth], "_")) names[depth] = bind(depth, "x");   /* an irrelevant binder needs a name: λ .x → */
        fprintf(out, " %s%s", (t->irr & 2) ? "." : "", names[depth]);
        depth++; t = t->a;
    }
    fputs(" → ", out); tp(t, depth, 0);
    if (prec > 0) fputc(')', out);
}
/* a cube constructor's method as written, \is -> inS t: the element t under the same lambdas (its type is the nested PathP) */
static Term *strip_ins(Term *m) {
    if (m->k == T_LAM) { Term *b = strip_ins(m->a); if (!b) return NULL; Term *r = mk_lam(m->name, b, m->irr); r->isi = m->isi; r->imp = m->imp; return r; }
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
static void app_print(Term *t, int depth, int prec) {
    if (t->k == T_APP && t->a->k == T_LAM) { tp(subst_term(t->a->a, 0, t->b), depth, prec); return; }   /* a beta redex (comp's desugaring: (\i -> A) i1): Agda cannot sort an applied bare lambda */
    Term *args[512]; int n = spine(t, args, 512);
    if (n < 0) { unsupported("spine too long"); return; }
    Term *h = spine_head(t);
    int nimp = 0, lvl = 0, nint = 0;   /* leading implicit arguments (a constructor's parameters), a level, missing intervals */
    if (h->k == T_CON) { Con *C = &cons[h->n]; Data *D = &datas[C->data]; nimp = D->nparams; lvl = D->poly; if (C->nint && n < nimp + C->nargs + C->nint) nint = nimp + C->nargs + C->nint - n; }
    if (nint && n < nimp + cons[h->n].nargs) { unsupported("a path constructor partially applied before its interval arguments"); nint = 0; }
    int paren = nint || (prec > 1 && (n > 0 || lvl || (h->k == T_DEF && defs[h->n].poly) || (h->k == T_DATA && datas[h->n].poly) || (h->k == T_ELIM && datas[h->n].poly)));
    if (paren) fputc('(', out);
    if (nint) { fputs("λ", out); for (int q = 0; q < nint; q++) { names[depth + q] = bind(depth + q, xsprintf("ι%d", q)); fprintf(out, " %s", names[depth + q]); } fputs(" → ", out); }
    int d2 = depth + nint;
    switch (h->k) {
    case T_CON: fputs(gname(T_CON, h->n), out); if (lvl) { fputs(" {", out); ref_level(h, d2); fputc('}', out); } break;
    case T_DEF: fputs(gname(T_DEF, h->n), out); if (defs[h->n].poly) { sp(); ref_level(h, d2); } break;
    case T_DATA: fputs(gname(T_DATA, h->n), out); if (datas[h->n].poly) { sp(); ref_level(h, d2); } break;
    case T_ELIM: fputs(gname(T_ELIM, h->n), out); if (datas[h->n].poly) { sp(); ref_level(h, d2); } break;
    default: tp(h, d2, 1); break;
    }
    for (int i = 0; i < n; i++) {
        if (i < nimp) { fputs(" {", out); tp(args[i], d2, 0); fputc('}', out); }
        else if (is_cube_method_arg(h, i)) { Term *m = strip_ins(args[i]); sp(); if (m) tp_arg(m, d2); else { unsupported("a cube method not of the form \\is -> inS t"); tp_arg(args[i], d2); } }
        else { sp(); tp_arg(args[i], d2); }
    }
    for (int q = 0; q < nint; q++) fprintf(out, " %s", names[depth + q]);
    if (paren) fputc(')', out);
}

static void tp(Term *t, int depth, int prec) {
    if (!t) { fputs("?", out); return; }
    switch (t->k) {
    case T_VAR: fputs(vname(depth, t->n), out); break;
    case T_U:
        if (prec > 1) fputc('(', out);
        fputs(t->pre ? "SSet " : "Set ", out);
        if (t->a) lt_print(t->a, depth, 2); else lv_const_print(t->n, 2);
        if (prec > 1) fputc(')', out);
        break;
    case T_LEVEL: fputs("Level", out); break;
    case T_LZERO: case T_LSUC: case T_LMAX: case T_LVAL: lt_print(t, depth, prec); break;
    case T_LMETA: unsupported("level meta"); break;
    case T_META: unsupported("unsolved meta ?%d", t->n); break;
    case T_DEF: case T_DATA: case T_CON: case T_ELIM: case T_APP: app_print(t, depth, prec); break;
    case T_NUM: {
        char *s = bn_to_dec(t->num);
        if (t->n == nat_builtin) fputs(s, out);
        else {
            unsigned long long v = strtoull(s, NULL, 10); int zi, si;
            if (strlen(s) > 4 || !peano_shape(t->n, &zi, &si)) unsupported("a literal %s of the data type %s, which is not the BUILTIN NATURAL", s, datas[t->n].name);
            else { if (prec > 1 && v) fputc('(', out); for (unsigned long long q = 0; q < v; q++) { fputs(gname(T_CON, si), out); sp(); } fputs(gname(T_CON, zi), out); if (prec > 1 && v) fputc(')', out); }
        }
        free(s); break; }
    case T_IRR: fputs("_", out); break;
    case T_INTERVAL: fputs("I", out); break;
    case T_I0: fputs("i0", out); break;
    case T_I1: fputs("i1", out); break;
    case T_INEG: if (prec > 1) fputc('(', out); fputs("~ ", out); tp(t->a, depth, 2); if (prec > 1) fputc(')', out); break;
    case T_IAND: fputc('(', out); tp(t->a, depth, 1); fputs(" ∧ ", out); tp(t->b, depth, 1); fputc(')', out); break;
    case T_IOR: fputc('(', out); tp(t->a, depth, 1); fputs(" ∨ ", out); tp(t->b, depth, 1); fputc(')', out); break;
    case T_PI: {
        if (prec > 0) fputc('(', out);
        int dep = term_mentions_var(t->b, 0);
        const char *nm = (!t->name || !strcmp(t->name, "_")) ? (dep ? bind(depth, "x") : "_") : bind(depth, t->name);
        if (!dep && !strcmp(nm, "_")) { tp(t->a, depth, 1); fputs(" → ", out); }
        else {
            fprintf(out, "%s(%s : ", (t->irr & 2) ? "." : "", nm);
            if (t->isi || t->a->k == T_INTERVAL) fputs("I", out); else tp(t->a, depth, 0);
            fputs(") → ", out);
        }
        names[depth] = nm; ktys[depth].ty = t->a; ktys[depth].depth = depth;   /* after the domain: its binders live at this level too */
        tp(t->b, depth + 1, 0);
        if (prec > 0) fputc(')', out);
        break; }
    case T_LAM: lam_print(t, depth, prec); break;
    case T_LET: {
        if (prec > 0) fputc('(', out);
        const char *nm = bind(depth, t->name);
        fprintf(out, "let %s : ", nm); tp(t->a, depth, 0); fprintf(out, " ; %s = ", nm); tp(t->b, depth, 0);
        names[depth] = nm; ktys[depth].ty = t->a; ktys[depth].depth = depth;
        fputs(" in ", out); tp(t->c, depth + 1, 0);
        if (prec > 0) fputc(')', out);
        break; }
    case T_PATHP:
        if (prec > 1) fputc('(', out);
        fputs("PathP ", out); implicit_level("ℓ", type_level(t, depth), depth); tp_arg(t->a, depth); sp(); tp_arg(t->b, depth); sp(); tp_arg(t->c, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_PAPP:
        if (prec > 1) fputc('(', out);
        tp(t->a, depth, 1); sp(); tp_arg(t->b, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_PARTIAL:
        if (prec > 1) fputc('(', out);
        fputs("Partial ", out); tp_arg(t->a, depth); sp(); tp_arg(t->b, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_SYS:
        if (sys_empty(t, depth)) fputs("(λ ())", out); else sys_print(t, depth);   /* the absurd clause: IsOne i0 is empty (isOneEmpty's type would be unsolved) */
        break;
    case T_TRANSP:
        if (prec > 1) fputc('(', out);
        fputs("transp ", out); tp_arg(t->a, depth); sp(); tp_arg(t->b, depth); sp(); tp_arg(t->c, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_HCOMP:
        if (prec > 1) fputc('(', out);
        fputs("hcomp {A = ", out); tp(t->a, depth, 0); fputs("} {φ = ", out); tp(t->b, depth, 0); fputs("} ", out); tp_arg(t->c, depth); sp(); tp_arg(t->d, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_SUB:
        if (prec > 1) fputc('(', out);
        fputs("Sub ", out); tp_arg(t->a, depth); sp(); tp_arg(t->b, depth); sp(); tp_parg(t->c, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_INS:
        if (prec > 1) fputc('(', out);
        fputs("inS ", out); tp_arg(t->a, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_OUTS: {
        Term *h = t->d; while (h->k == T_APP || h->k == T_PAPP) h = h->a;
        if (h->k == T_VAR) { int lvl = depth - 1 - h->n; Term *kt = (lvl >= 0 && lvl < depth) ? ktys[lvl].ty : NULL;
            if (kt && kt->k == T_PATHP) { tp(t->d, depth, prec); break; } }   /* the element of a cube method: in Agda the method is the path itself */
        if (prec > 1) fputc('(', out);
        fputs("outS {A = ", out); tp(t->a, depth, 0); fputs("} {φ = ", out); tp(t->b, depth, 0); fputs("} {u = ", out); tp(t->c, depth, 0); fputs("} ", out); tp_arg(t->d, depth);
        if (prec > 1) fputc(')', out);
        break; }
    case T_SIGMA: {
        if (prec > 1) fputc('(', out);
        fputs(t->irr ? "Σᵢ " : "Σ ", out);
        { Term *la = type_level(t->a, depth); binder_open(t, depth); Term *lb = type_level(t->b, depth + 1);
          if (la && lb) { implicit_level("a", la, depth); implicit_level("b", lb, depth + 1); } }
        tp_arg(t->a, depth);
        binder_open(t, depth);
        if (!strcmp(names[depth], "_")) names[depth] = bind(depth, "x");
        fprintf(out, " (λ %s → ", names[depth]); tp(t->b, depth + 1, 0); fputc(')', out);
        if (prec > 1) fputc(')', out);
        break; }
    case T_PAIR: fputc('(', out); tp(t->a, depth, 1); fputs((t->irr || t->n == 1) ? " ,ᵢ " : " , ", out); tp(t->b, depth, 1); fputc(')', out); break;   /* a lambda component parenthesized: its body would swallow the comma */
    case T_FST: if (prec > 1) fputc('(', out); fputs((t->irr || t->n == 1) ? "fstᵢ " : "fst ", out); tp_arg(t->a, depth); if (prec > 1) fputc(')', out); break;
    case T_SND: if (prec > 1) fputc('(', out); fputs((t->irr || t->n == 1) ? "sndᵢ " : "snd ", out); tp_arg(t->a, depth); if (prec > 1) fputc(')', out); break;
    case T_GLUE:
        if (prec > 1) fputc('(', out);
        fputs("G.primGlue ", out); implicit_level("ℓ", type_level(t->a, depth), depth); implicit_level("ℓ'", t->d ? t->d : lvl_const(t->n), depth);
        tp_arg(t->a, depth); fputs(" {φ = ", out); tp(t->b, depth, 0); fputs("} ", out); glue_T(t->c, depth); sp(); glue_e(t->c, depth);
        if (prec > 1) fputc(')', out);
        break;
    case T_GLUEEL: {
        Term *g = t->c;
        if (prec > 1) fputc('(', out);
        fputs("G.prim^glue", out);
        if (g && g->k == T_GLUE) { sp(); implicit_level("ℓ", type_level(g->a, depth), depth); implicit_level("ℓ'", g->d ? g->d : lvl_const(g->n), depth); fputs("{A = ", out); tp(g->a, depth, 0); fputs("} {φ = ", out); tp(g->b, depth, 0); fputs("} {T = ", out); glue_T(g->c, depth); fputs("} {e = ", out); glue_e(g->c, depth); fputc('}', out); }
        sp(); tp_parg(t->a, depth); sp(); tp_arg(t->b, depth);
        if (prec > 1) fputc(')', out);
        break; }
    case T_UNGLUE:
        if (prec > 1) fputc('(', out);
        fputs("G.prim^unglue ", out); implicit_level("ℓ", type_level(t->b, depth), depth); fputs("{A = ", out); tp(t->b, depth, 0); fputs("} {φ = ", out); tp(t->c, depth, 0); fputs("} {T = ", out); glue_T(t->d, depth); fputs("} {e = ", out); glue_e(t->d, depth); fputs("} ", out); tp_arg(t->a, depth);
        if (prec > 1) fputc(')', out);
        break;
    }
}

/* ---------------- declarations ---------------- */

static void level_binder(int depth, const char *nm, int explicit_) {
    names[depth] = nm; ktys[depth].ty = NULL;
    fprintf(out, explicit_ ? "(%s : Level) → " : "{%s : Level} → ", nm);
}

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
        binder_open(v, depth); ktys[depth].ty = ty->a; ktys[depth].depth = depth;
        fprintf(out, " %s", names[depth]);   /* a clause variable: irrelevance comes from the signature (a dot here would be an inaccessible pattern) */
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
        names[depth0 + i] = nm; ktys[depth0 + i].ty = D->ptys[i]; ktys[depth0 + i].depth = depth0 + i;
    }
}
/* data D (ℓd)? (params) : (indices) → Set lvl */
static void data_sig(int d, int with_where) {
    Data *D = &datas[d];
    ownlvl = D->poly ? "ℓd" : NULL;
    int depth = 0;
    fprintf(out, "data %s", gname(T_DATA, d));
    if (D->poly) { names[depth] = "ℓd"; ktys[depth].ty = NULL; fputs(" (ℓd : Level)", out); depth++; }
    data_params(D, depth); depth += D->nparams;
    fputs(" : ", out);
    for (int j = 0; j < D->nidx; j++) {
        const char *nm = bind(depth, xsprintf("i%d", j));
        fprintf(out, "(%s : ", nm); tp(D->itys[j], depth, 0); fputs(") → ", out);
        names[depth] = nm; ktys[depth].ty = D->itys[j]; ktys[depth].depth = depth; depth++;
    }
    fputs("Set ", out); lv_print(D->lvl, depth, 2);
    fputs(with_where ? " where\n" : "\n", out);
}
/* the constructors of D (under 'data D where' or the combined declaration) */
static void data_cons(int d) {
    Data *D = &datas[d];
    ownlvl = D->poly ? "ℓd" : NULL;
    int depth = 0;
    if (D->poly) { names[depth++] = "ℓd"; }
    for (int i = 0; i < D->nparams; i++) { names[depth] = bind(depth, xsprintf("p%d", i)); ktys[depth].ty = D->ptys[i]; ktys[depth].depth = depth; depth++; }
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
            names[dep] = nm; ktys[dep].ty = A->ty; ktys[dep].depth = dep;
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
            for (int q = 0; q < n; q++) { names[dep + q] = bind(dep + q, xsprintf("i%d", q)); ktys[dep + q].ty = NULL; }
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
        names[depth] = nm; ktys[depth].ty = dom; ktys[depth].depth = depth;
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
        if (D->poly) { names[dep] = "ℓd"; ktys[dep].ty = NULL; fputs(" ℓd", out); dep++; }
        for (int i = 0; i < np; i++) { pn[i] = names[dep] = bind(dep, xsprintf("p%d", i)); ktys[dep].ty = D->ptys[i]; ktys[dep].depth = dep; fprintf(out, " %s", pn[i]); dep++; }
        int pdep = dep;   /* [ℓd?, params] */
        for (int i = 0; i < nbk; i++) { Pn[i] = names[dep] = bind(dep, xsprintf("P%d", i)); ktys[dep].ty = NULL; fprintf(out, " %s", Pn[i]); dep++; }
        for (int i = 0; i < K; i++) { mn[i] = names[dep] = bind(dep, xsprintf("m%d", i)); ktys[dep].ty = NULL; fprintf(out, " %s", mn[i]); dep++; }
        for (int j = 0; j < m; j++) fputs(" _", out);
        /* the constructor pattern: its arguments are named at levels pdep.. so that index terms print under [params, args] */
        fprintf(out, " (%s", gname(T_CON, D->cons[ci]));
        const char **an = xalloc((r + 1) * sizeof(char *));
        for (int j = 0; j < r; j++) { an[j] = names[pdep + j] = bind(pdep + j, C->args[j].name && strcmp(C->args[j].name, "_") ? C->args[j].name : xsprintf("a%d", j)); ktys[pdep + j].ty = C->args[j].ty; ktys[pdep + j].depth = pdep + j; fprintf(out, " %s", an[j]); }
        const char **in = xalloc((C->nint + 1) * sizeof(char *));
        for (int q = 0; q < C->nint; q++) { in[q] = names[pdep + r + q] = bind(pdep + r + q, xsprintf("j%d", q)); fprintf(out, " %s", in[q]); }
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
            for (int y = 0; y < q; y++) { names[ydep + y] = bind(ydep + y, A->isrecpath ? "k" : xsprintf("y%d", y)); ktys[ydep + y].ty = NULL; fprintf(out, " %s", names[ydep + y]); }
            fprintf(out, q ? " → %s {ℓ}" : "%s {ℓ}", gname(T_ELIM, rm));
            if (RM->poly) fputs(" ℓd", out);
            for (int i = 0; i < np; i++) fprintf(out, " %s", pn[i]);
            for (int i = 0; i < nbk; i++) fprintf(out, " %s", Pn[i]);
            for (int i = 0; i < K; i++) fprintf(out, " %s", mn[i]);
            if (!A->isrecpath) for (int i = 0; i < A->nidx; i++) { sp(); tp_arg(A->idx[i], ydep + q); }
            if (q) { fprintf(out, " (%s", an[j]); for (int y = 0; y < q; y++) fprintf(out, " %s", names[ydep + y]); fputs("))", out); }
            else fprintf(out, " %s)", an[j]);
            /* restore the argument names shadowed by the y binders */
            for (int y = 0; y < q && j + y < r; y++) names[pdep + j + y] = an[j + y];
            for (int y = 0; y < q; y++) if (j + y >= r && j + y < r + C->nint) names[pdep + j + y] = in[j + y - r];
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
static char *needdef, *needdata;
static void need_term(Term *t);
static void need_data(int d) {
    Data *D = &datas[d]; if (needdata[d]) return;
    for (int k = 0; k < D->nblock; k++) {   /* a block is printed whole */
        int m = D->block + k; if (needdata[m]) continue; needdata[m] = 1;
        Data *M = &datas[m];
        for (int i = 0; i < M->nparams; i++) need_term(M->ptys[i]);
        for (int j = 0; j < M->nidx; j++) need_term(M->itys[j]);
        for (int ci = 0; ci < M->ncons; ci++) {
            Con *C = &cons[M->cons[ci]];
            for (int j = 0; j < C->nargs; j++) need_term(C->args[j].ty);
            for (int j = 0; j < M->nidx; j++) need_term(C->ridx[j]);
            if (C->boundary) need_term(C->boundary);
        }
    }
}
static void need_def(int i) { if (needdef[i]) return; needdef[i] = 1; need_term(defs[i].ty); need_term(defs[i].val); }
static void need_term(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF: need_def(t->n); need_term(t->a); return;
    case T_DATA: case T_ELIM: need_data(t->n); need_term(t->a); return;
    case T_CON: need_data(cons[t->n].data); need_term(t->a); return;
    case T_NUM: need_data(t->n); need_term(t->a); return;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { need_term(t->br[i].face); need_term(t->br[i].body); } return;
    default: need_term(t->a); need_term(t->b); need_term(t->c); need_term(t->d); return;
    }
}

int agda_program(FILE *f, const char *modname, int first_seq) {
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
    if (nunsup) fprintf(out, "-- %d unsupported construct%s: this module is not a faithful image of the program\n", nunsup, nunsup == 1 ? "" : "s");
    return nunsup ? 3 : 0;
}
