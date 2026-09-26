/*
 * erase.c - erasure of checked programs to eezoc source.
 *
 * Types are not dropped: they erase to run-time codes (a Tarski universe),
 * because transport along a line of types is the execution of a recipe and
 * must survive to run time.  A code is a record  k -> k(method)(c1)..(cn)
 * whose method is its own transport rule:
 *   tt_transp line phi a = phi(a)(line(i0)(m -> m)(line)(phi)(a))
 * so the code at the start of a line dispatches the transport along the
 * whole line.  tc_u (identity), tc_pi (the CCHM rule for functions),
 * tc_path (composition in the underlying line), and one tc_D per data type
 * whose method transports constructor arguments along their own type lines
 * with fillers, exactly as the checker does.  Binders of type-like type are
 * therefore relevant; only the positions that never carry run-time content
 * vanish: data-type parameters of constructors and eliminators, motives,
 * indices.  Constructors become Scott selectors and induction a recursive
 * case analysis built with the prelude's fix.  The interval is three-valued
 * Scott data, i0, half and i1, with Kleene's tables: a closed face is i0 or
 * i1 and selects (tt_sel); half is the symbol of tt_forall, since a face is
 * 1 in the free De Morgan algebra on one generator exactly when it is 1 at
 * half (Kleene's chain is a De Morgan algebra and the map is injective on
 * 0 and 1), and a face never contains a transport, so one symbol is enough.
 * Faces are erased in sorted disjunctive normal form, so the same face
 * erases to the same term whether it comes from a source program or from a
 * quoted normal form.  hcomp is the choice between its sides at i1 and its
 * base.  hcomp in the universe has no run-time meaning before Glue and is
 * refused.  eezoc expands a definition at every reference, so the run-time
 * prelude must stay small.
 * Output is ordinary eezoc source: definitions in dependency order, then
 * `;` and the program's main term.
 */
#include "tt.h"
#include <stdlib.h>

int keep_kan, nf_main;
/* One Nat (M19). A data type shaped like the naturals runs as the representation an equivalence in scope names:
   for each such type d, exactly one definition of type Equiv d R (the prelude's Equiv, the notion Glue is built on,
   the one definition this file knows by name) makes R the run-time type of d, and every role of the erasure - the
   constructors, the case analysis (answered in a two-constructor data type whose first constructor is its true),
   the word boundary, the natives, the digits of a literal - is the implementation the SHAPE of a law in scope
   names: a pattern with metavariables is unified against the type of every definition, and the implementation is
   read off the solution. A role with two laws is refused as ambiguous; a native with no law erases as its own body
   (a fold over the interface); a representation with no digit laws converts its literals through the
   equivalence's own forward map, evaluated by the checker. Nothing else is found by name. */
enum { NR_ADD = 1, NR_SUB, NR_MUL, NR_DIV, NR_MOD, NR_POW, NR_EQ, NR_LT, NR_LE, NR_MINV, NR_COUNT };   /* native_code's order */
typedef struct {
    int d, zi, si;                   /* the data type, its zero and its successor */
    int equiv;                       /* the definition of type Equiv d R */
    Term *R, *g;                     /* the run-time type; the value map R -> d the laws are stated with (the equivalence's inverse) */
    Term *zero, *suc, *isz, *pred;   /* the interface */
    Term *single, *low;              /* the word boundary: a word's value, a value's low word (NULL: no law) */
    Term *native[NR_COUNT];          /* by code (NULL: no law, the body runs) */
    int native_direct[NR_COUNT];     /* the law reads h x y = f (g x) (g y): the operation answers in d itself (a decision) */
    Term *P, *gP, *npos, *top, *cons;   /* the digits (NULL: none): the positive type and its value map, the injection, the top word, a word under a numeral */
} Rep;
static Rep *reps; static int nreps;
static Rep *rep_of(int d) { for (int i = 0; i < nreps; i++) if (reps[i].d == d) return &reps[i]; return NULL; }
static int is_nat(int d) { return rep_of(d) != NULL; }   /* runs as a representation */
static Rep *rep_need(int d, const char *what) {
    Rep *r = d >= 0 ? rep_of(d) : NULL;
    if (!r) die("%s: %s has no run-time representation (no equivalence in scope)", what, d >= 0 ? datas[d].name : "the word type's naturals");
    return r;
}
static Term *role_need(Term *t, const char *what) {
    if (!t) die("the run-time representation has no law for %s", what);
    return t;
}
static int native_dom(int def) {   /* the data type a native computes on: the domain of its type, or -1 */
    Val *ty = force(defs[def].vty);
    if (ty->k != V_PI) return -1;
    Val *dom = force(ty->dom);
    return dom->k == V_DATA ? dom->n : -1;
}
static int native_of(int d, int code) {   /* the native of that code on d, or -1 */
    for (int i = 0; i < ndefs; i++) if (defs[i].native == code && native_dom(i) == d) return i;
    return -1;
}
static Term *literal_via_map(Rep *r, Term *t);
static void erase_literal(Rep *r, Term *t, int depth);
static int rep_trace = -1;   /* EEZOTT_REP_TRACE: print each role's and scheme's match */
static FILE *out;
static int self_data = -1;      /* while emitting tc_D: references to D are the fixpoint's self */
static void emit_sel(int nb, int m);
static void erase(Term *t, int depth);

/* An elimination on the Nat is answered by the representation's interface (M16b C3, M17, M18). A method that
   does not use its induction hypothesis is a case analysis: the empty test selects the zero method, else the
   successor method gets the predecessor and a dummy for the hypothesis - one word operation each. A method that
   uses its hypothesis is a fold: the closed form when a theorem licenses one (fold.tt), and otherwise the walk,
   predecessor by predecessor - one word operation per step, as many steps as the value, as the checker's own
   elimination. The walk is the default; a closed form is licensed by a theorem, never guessed. */
static Term *strip_lams(Term *t, int k) {
    while (t && k > 0 && t->k == T_LAM) { t = t->a; k--; }
    return k > 0 ? NULL : t;
}
/* The prelude's def with this name, or -1 (the folds below reach for add and mul by name) */
static int def_named(const char *name) {
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, name)) return i;
    return -1;
}
/* a def applied to arguments, built as a term for the ordinary erasure to emit */
static Term *mk_defapp(int d, Term **args, int nargs) {
    Term *t = xalloc(sizeof *t);
    t->k = T_DEF; t->n = d;
    for (int i = 0; i < nargs; i++) {
        Term *ap = xalloc(sizeof *ap);
        ap->k = T_APP; ap->a = t; ap->b = args[i];
        t = ap;
    }
    return t;
}
/* The closed form of an elimination whose method uses its hypothesis is what a theorem in scope licenses (M19, S3): a
   definition whose type, under its binders, is Path d (elim d M Z S n) R. Its binders become metavariables in the
   elimination's own context, its left side is unified with the elimination, and its right side, with the solutions,
   is the form emitted - evaluated first, so a literal scrutinee is computed by the checker. Two theorems for one
   elimination are refused; none, and the elimination walks. A step of j successors is first read as the addition
   of j, its definitional equal, so the theorem about additions applies to it. */
static int scheme_theorem(Val *ty, int d) {   /* the shape: binders, then a path from an elimination on d */
    int i = 0;
    for (;;) { Val *t = fmeta(ty); if (t->k != V_PI) t = force(ty); if (t->k != V_PI) break; ty = inst(&t->clo, t->isi ? vivar(i) : vvar(i)); i++; }
    Val *t = fmeta(ty); if (t->k != V_PATHP) t = force(ty); if (t->k != V_PATHP) return 0;
    Val *l = fmeta(t->b);
    return l->k == V_NEU && l->h == H_ELIM && l->n == d;
}
static Term *canon_step(Rep *rep, Term *body) {   /* suc^j ih (j >= 1) is add j ih; else the step as written */
    int addd = native_of(rep->d, NR_ADD); if (addd < 0) return body;
    Term *b = body; int j = 0;
    while (b->k == T_APP && b->a->k == T_CON && b->a->n == rep->si) { b = b->b; j++; }
    if (j == 0 || b->k != T_VAR || b->n != 0) return body;
    Term *jlit = mk_num(rep->d, NULL, bn_from_u64((u64)j));
    Term *args[2] = { jlit, mk_var(0) };
    return mk_defapp(addd, args, 2);
}
static Term *scheme_closed_form(Rep *rep, Term *elimapp, int depth) {
    Env *env = NULL; for (int i = 0; i < depth; i++) env = env_push(env, vvar(i));
    const char **names = xalloc((depth + 1) * sizeof(char *)); for (int i = 0; i < depth; i++) names[i] = "v";
    Val *ev = eval(env, elimapp);
    Term *best = NULL; int hits = 0; const char *n1 = NULL, *n2 = NULL;
    for (int i = 0; i < ndefs; i++) {
        if (!scheme_theorem(defs[i].vty, rep->d)) continue;
        MMark mk = meta_mark(); int m0 = ntmetas;
        Val *ty = defs[i].vty;
        for (;;) {   /* the theorem's binders, as metas of the elimination's context */
            Val *t = fmeta(ty); if (t->k != V_PI) t = force(ty); if (t->k != V_PI) { ty = t; break; }
            int id = meta_new(t->dom, depth, names, 0);
            ty = inst(&t->clo, eval(env, meta_term(id, depth)));
        }
        int ok = ty->k == V_PATHP && conv(depth, ev, ty->b) && metas_retry();
        for (int k = m0; ok && k < ntmetas; k++) if (!meta_solved(k)) ok = 0;
        if (ok) { hits++; n2 = n1; n1 = defs[i].name; best = quote(depth, eval(env, zonk(quote(depth, ty->c)))); }
        if (rep_trace < 0) rep_trace = getenv("EEZOTT_REP_TRACE") != NULL;
        if (rep_trace) fprintf(stderr, "[scheme] %s in %s: %s\n", defs[i].name, cur_decl_name ? cur_decl_name : "main", ok ? "licenses the closed form" : "does not apply");
        meta_rollback(mk);
    }
    if (hits > 1) die("the closed form of an elimination in %s is ambiguous: %s and %s both license one", cur_decl_name ? cur_decl_name : "main", n2, n1);
    return best;
}
static void visit(Term *t);
static int *def_state, *data_state;   /* 0 unseen, 1 being emitted, 2 emitted */
/* every definition a term refers to at run time (natives through the representation's operations) is in the wanted state:
   2, emitted, for a closed form about to be emitted; not 1, being emitted, for a theorem's right side about to be visited -
   a closed form inside the representation's own operations would reach them, so there the elimination walks */
static int term_defs_ok(Term *t, int want) {
    if (!t) return 1;
    switch (t->k) {
    case T_DEF:
        if (defs[t->n].native) { Rep *r = rep_of(native_dom(t->n)); if (r && r->native[defs[t->n].native]) return term_defs_ok(r->native[defs[t->n].native], want); }
        if (defs[t->n].wordop || defs[t->n].isword) return 1;
        return want == 2 ? def_state[t->n] == 2 : def_state[t->n] != 1;
    case T_CON: { Rep *r = rep_of(cons[t->n].data); return r ? term_defs_ok(cons[t->n].nargs == 0 ? r->zero : r->suc, want) : 1; }
    case T_DATA: { Rep *r = rep_of(t->n); return r ? term_defs_ok(r->R, want) : 1; }
    case T_ELIM: { Rep *r = rep_of(t->n); return r ? term_defs_ok(r->isz, want) && term_defs_ok(r->pred, want) : 1; }
    case T_SYS: for (int i = 0; i < t->nbr; i++) if (!term_defs_ok(t->br[i].face, want) || !term_defs_ok(t->br[i].body, want)) return 0; return 1;
    default: return term_defs_ok(t->a, want) && term_defs_ok(t->b, want) && term_defs_ok(t->c, want) && term_defs_ok(t->d, want);
    }
}
static void visit_scheme_rhs(Rep *rep) {   /* the right sides of the scheme theorems in scope, under their binders */
    for (int i = 0; i < ndefs; i++) {
        if (!scheme_theorem(defs[i].vty, rep->d)) continue;
        Val *ty = defs[i].vty; int k = 0;
        for (;;) { Val *t = fmeta(ty); if (t->k != V_PI) t = force(ty); if (t->k != V_PI) { ty = t; break; } ty = inst(&t->clo, t->isi ? vivar(k) : vvar(k)); k++; }
        if (ty->k == V_PATHP) { Term *r = quote(k, ty->c); if (term_defs_ok(r, 1)) visit(r); }
    }
}
/* an elimination on the Nat: emitted (emit) or its references walked for the dependency order (not emit) */
static int nat_elim_spine(Term *t, int depth, int emit) {
    Term *node[8]; int n = 0; Term *h = t;
    while (h->k == T_APP) { if (n < 8) node[n] = h; n++; h = h->a; }
    if (h->k != T_ELIM || !is_nat(h->n)) return 0;
    Rep *rep = rep_of(h->n);
    if (n > 8) die("an elimination on the Nat is applied to more arguments than the erasure can see through");
    /* the eliminator's own arguments are the innermost four: the motive (irrelevant, so never emitted), the
       methods in constructor order, and the scrutinee; anything outside them applies the elimination's result */
    if (n < 4) {   /* partially applied (a point-free definition): eta-expanded - the missing arguments become binders */
        int k = 4 - n;
        Term *t2 = shift(t, 0, k);
        for (int i = k - 1; i >= 0; i--) { Term *v = xalloc(sizeof *v); v->k = T_VAR; v->n = i; Term *ap = xalloc(sizeof *ap); ap->k = T_APP; ap->a = t2; ap->b = v; t2 = ap; }
        if (emit) for (int i = 0; i < k; i++) fprintf(out, "(v%d -> ", depth + i);
        int r = nat_elim_spine(t2, depth + k, emit);
        if (emit) for (int i = 0; i < k; i++) fputc(')', out);
        return r;
    }
    int extra = n - 4;
    Term *motive = node[n - 1]->b, *mz = node[n - 2]->b, *ms = node[n - 3]->b, *scrut = node[n - 4]->b;
    (void)motive;
    Term *meth = ms;
    if (meth->k == T_DEF) meth = defs[meth->n].val;   /* the checker sees through a definition application; so does the erasure */
    Term *body = strip_lams(meth, 2);
    if (!body) die("an elimination's method must be a function of its predecessor and its induction hypothesis");
    /* The methods live in the context outside the binder v<depth> introduced here and never mention it, so they
       are erased at that depth (a binder of their own may reuse the name inside its own scope, harmlessly).
       The empty test is a Bool: true selects its first handler, the zero case. */
    Term *isz = role_need(rep->isz, "an elimination's zero test"), *pred = role_need(rep->pred, "an elimination's predecessor");
    if (!emit) {   /* the dependency walk: what the emission below may refer to - the walk's parts, and, for a fold, the right
                      sides of the theorems in scope (a closed form is built from them and from the elimination's own terms) */
        visit(isz); visit(pred); visit(mz); visit(ms); visit(scrut);
        if (term_mentions_var(body, 0)) visit_scheme_rhs(rep);
        for (int i = extra - 1; i >= 0; i--) if (!node[i]->irr) visit(node[i]->b);
        return 1;
    }
    Term *closed = NULL;
    if (term_mentions_var(body, 0)) {   /* a fold: the closed form a theorem licenses, if one does */
        Term *body2 = canon_step(rep, body);
        Term *ms2 = body2 == body ? ms : mk_lam("k", mk_lam("ih", body2, 0), 0);
        Term *e = mk_app(mk_app(mk_app(node[n - 1], mz, node[n - 2]->irr), ms2, node[n - 3]->irr), scrut, node[n - 4]->irr);
        closed = scheme_closed_form(rep, e, depth);
        if (closed && !term_defs_ok(closed, 2)) closed = NULL;   /* its parts are not all emitted (a cycle through the representation): the walk */
    }
    if (term_mentions_var(body, 0)) {
        if (closed) erase(closed, depth);
        else {   /* the walk: fix over the predecessor */
            fprintf(out, "(fix(self -> v%d -> ", depth); erase(isz, depth); fprintf(out, "(v%d)(", depth); erase(mz, depth);
            fputs(")(", out); erase(ms, depth); fputc('(', out); erase(pred, depth); fprintf(out, "(v%d))(self(", depth); erase(pred, depth); fprintf(out, "(v%d))))))(", depth);
            erase(scrut, depth); fputc(')', out);
        }
    } else {   /* the case analysis: the predecessor, and a dummy for the induction hypothesis */
        fprintf(out, "((v%d -> ", depth); erase(isz, depth); fprintf(out, "(v%d)(", depth); erase(mz, depth);
        fputs(")(", out); erase(ms, depth); fputc('(', out); erase(pred, depth); fprintf(out, "(v%d))(tc_u)))(", depth);
        erase(scrut, depth); fputs("))", out);
    }
    for (int i = extra - 1; i >= 0; i--) if (!node[i]->irr) { fputc('(', out); erase(node[i]->b, depth); fputc(')', out); }
    return 1;
}
static int try_nat_elim(Term *t, int depth) { return nat_elim_spine(t, depth, 1); }


/* a face term to the checker's interval algebra, interval variables by their erased index (v<index> = level depth-1-n) */
static IVal face_ival(Term *t, int depth) {
    switch (t->k) {
    case T_VAR: return iv_var(depth - 1 - t->n);
    case T_I0: return iv_zero();
    case T_I1: return iv_one();
    case T_IAND: return iv_and(face_ival(t->a, depth), face_ival(t->b, depth));
    case T_IOR: return iv_or(face_ival(t->a, depth), face_ival(t->b, depth));
    case T_INEG: return iv_neg(face_ival(t->a, depth));
    default: die("internal: a face that is not an interval term"); return iv_zero();
    }
}
static int lit_cmp(const void *x, const void *y) { const ILit *a = x, *b = y; return a->var != b->var ? a->var - b->var : a->neg - b->neg; }
static int conj_cmp(const void *x, const void *y) {
    const IConj *a = x, *b = y;
    for (int i = 0; i < a->n && i < b->n; i++) { int c = lit_cmp(&a->l[i], &b->l[i]); if (c) return c; }
    return a->n - b->n;
}
/* the face in sorted disjunctive normal form: tt_ior of tt_iand of literals */
static void erase_face(Term *t, int depth) {
    IVal v = face_ival(t, depth);
    if (iv_is_zero(v)) { fputs("tt_i0", out); return; }
    if (iv_is_one(v)) { fputs("tt_i1", out); return; }
    IConj *cs = xalloc((v.n + 1) * sizeof(IConj));
    for (int i = 0; i < v.n; i++) {
        cs[i].n = v.c[i].n; cs[i].l = xalloc((cs[i].n + 1) * sizeof(ILit));
        for (int j = 0; j < cs[i].n; j++) cs[i].l[j] = v.c[i].l[j];
        qsort(cs[i].l, cs[i].n, sizeof(ILit), lit_cmp);
    }
    qsort(cs, v.n, sizeof(IConj), conj_cmp);
    for (int i = 0; i + 1 < v.n; i++) fputs("tt_ior(", out);
    for (int i = 0; i < v.n; i++) {
        if (i) fputs(")(", out);
        for (int j = 0; j + 1 < cs[i].n; j++) fputs("tt_iand(", out);
        for (int j = 0; j < cs[i].n; j++) {
            if (j) fputs(")(", out);
            if (cs[i].l[j].neg) fprintf(out, "tt_ineg(v%d)", cs[i].l[j].var); else fprintf(out, "v%d", cs[i].l[j].var);
        }
        for (int j = 0; j + 1 < cs[i].n; j++) fputc(')', out);
    }
    for (int i = 0; i + 1 < v.n; i++) fputc(')', out);
}
static void erase(Term *t, int depth) {
    switch (t->k) {
    case T_META: die("internal: a metavariable reached erasure");
    case T_VAR: fprintf(out, "v%d", depth - 1 - t->n); break;
    case T_LAM:
        if (t->irr) { erase(t->a, depth + 1); break; }
        fprintf(out, "(v%d -> ", depth); erase(t->a, depth + 1); fputc(')', out); break;
    case T_APP:
        if (try_nat_elim(t, depth)) break;   /* an elimination on the Nat: the representation's interface */
        erase(t->a, depth);
        if (!t->irr) { fputc('(', out); erase(t->b, depth); fputc(')', out); }
        break;
    case T_PAPP: erase(t->a, depth); fputc('(', out); erase(t->b, depth); fputc(')', out); break;
    case T_LET:
        if (t->irr) { erase(t->c, depth + 1); break; }
        fprintf(out, "((v%d -> ", depth); erase(t->c, depth + 1); fputs(")(", out); erase(t->b, depth); fputs("))", out); break;
    case T_DEF:
        if (defs[t->n].native) {   /* a native is the representation's operation its law names; without a law, its own body */
            Rep *r = rep_of(native_dom(t->n));
            if (r && r->native[defs[t->n].native]) { erase(r->native[defs[t->n].native], depth); break; }
        }
        if (defs[t->n].wordop) fputs(wordop_name(defs[t->n].wordop), out);   /* a word operation is its run-time primitive */
        else if (defs[t->n].isword) fputs("tc_u", out);                     /* the word type: a machine word normalizes to itself */
        else fprintf(out, "tt_%s", defs[t->n].name);
        break;
    case T_NUM: {
        Rep *r = rep_of(t->n);
        if (r) { erase_literal(r, t, depth); break; }   /* the representation's digits, or its forward map */
        erase(numeral_term(t->n, t->a, t->num), depth); break;   /* a literal is spelled out in constructors, O(log n) */
    }
    case T_IRR: fputs("tc_u", out); break;
    case T_CON:
        { Rep *r = rep_of(cons[t->n].data);
          if (r) { erase(role_need(cons[t->n].nargs == 0 ? r->zero : r->suc, cons[t->n].name), depth); break; } }   /* the representation's zero and successor */
        fprintf(out, "tt_c_%s", cons[t->n].name); break;
    case T_ELIM:
        if (is_nat(t->n)) die("an elimination on the Nat is compiled from its whole spine, so it cannot be erased head-first");
        fprintf(out, "tt_rec_%s", datas[t->n].name); break;
    case T_DATA:   /* inside a code: the block's own codes are the fixpoint variable (a selector of the tuple for a block of several) */
        { Rep *r = rep_of(t->n); if (r) { erase(r->R, depth); break; } }   /* the representation's type is the Nat's code */
        if (self_data >= 0 && datas[t->n].block == datas[self_data].block) {
            if (datas[t->n].nblock == 1) fputs("self", out);
            else { fputs("selfs(", out); emit_sel(datas[t->n].nblock, datas[t->n].bpos); fputc(')', out); }
        } else fprintf(out, "tc_%s", datas[t->n].name);
        break;
    case T_U: case T_INTERVAL: case T_PARTIAL: case T_SUB: case T_LEVEL: case T_LZERO: case T_LSUC: case T_LMAX: case T_LMETA: case T_LVAL: fputs("tc_u", out); break;
    case T_PI: fputs("tc_pi(", out); erase(t->a, depth); fprintf(out, ")(v%d -> ", depth); erase(t->b, depth + 1); fputc(')', out); break;
    case T_PATHP: fputs("tc_path(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_I0: case T_I1: case T_IAND: case T_IOR: case T_INEG: erase_face(t, depth); break;
    case T_SYS:   /* a system selects its first branch whose face holds */
        for (int i = 0; i < t->nbr; i++) { fputs("tt_sel(", out); erase_face(t->br[i].face, depth); fputs(")(", out); erase(t->br[i].body, depth); fputs(")(", out); }
        fputs("tt_absurd", out);
        for (int i = 0; i < t->nbr; i++) fputc(')', out);
        break;
    case T_HCOMP:
        if (t->n) { fputs("tt_hcompU(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputc(')', out); break; }
        fputs("tt_hcomp(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputc(')', out); break;
    case T_TRANSP:
        if (!keep_kan && (t->n || t->b->k == T_I1)) { erase(t->c, depth); break; }     /* a constant line: the identity */
        fputs("tt_transp(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_INS: erase(t->a, depth); break;
    case T_OUTS: erase(t->d, depth); break;
    case T_SIGMA:
        if (t->irr) { erase(t->a, depth); break; }   /* an irrelevant second component: at run time the type is its first (M16a, for every such type) */
        fputs("tc_sigma(", out); erase(t->a, depth); fprintf(out, ")(v%d -> ", depth); erase(t->b, depth + 1); fputc(')', out); break;
    case T_PAIR:
        if (t->n) {   /* at the word type: the machine word */
            if (t->a->k == T_NUM) { char *s = bn_to_dec(t->a->num); fprintf(out, "%sw", s); free(s); }
            else { erase(role_need(rep_need(word_nat, "a word from a value")->low, "a value's low word"), depth); fputc('(', out); erase(t->a, depth); fputc(')', out); }   /* the representation's low word */
            break;
        }
        if (t->irr) { erase(t->a, depth); break; }   /* an irrelevant second component: the pair is its first */
        fputs("tt_pair(", out); erase(t->a, depth); fputs(")(", out);
        if (t->irr) fputs("tc_u", out); else erase(t->b, depth);   /* an irrelevant component has no run-time content */
        fputc(')', out); break;
    case T_FST:
        if (t->n) { erase(role_need(rep_need(word_nat, "a word's value")->single, "a word's value"), depth); fputc('(', out); erase(t->a, depth); fputc(')', out); break; }   /* a word's value: the representation's one-word numeral */
        if (t->irr) { erase(t->a, depth); break; }
        fputs("tt_fst(", out); erase(t->a, depth); fputc(')', out); break;
    case T_SND:
        if (t->n || t->irr) { fputs("tc_u", out); break; }
        fputs("tt_snd(", out); erase(t->a, depth); fputc(')', out); break;
    case T_GLUE: fputs("tc_glue(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_GLUEEL: fputs("tt_glue(", out); erase(t->c->b, depth); fputs(")(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputc(')', out); break;
    case T_UNGLUE: fputs("tt_unglue(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputs(")(", out); erase(t->a, depth); fputc(')', out); break;
    }
}

/* hcomp is a formal element (an extra constructor) of higher inductive types and indexed families, as in the checker */
static int formal_hcomp(Data *D) { return D->hit || D->nidx > 0; }
/* the selector of member m of a tuple of nb: r0 -> .. -> r_{nb-1} -> r_m */
static void emit_sel(int nb, int m) { for (int i = 0; i < nb; i++) fprintf(out, "r%d -> ", i); fprintf(out, "r%d", m); }
static int nhandlers(Data *D) { return D->ncons + formal_hcomp(D); }
/* Scott constructor: relevant args, then one handler per constructor, select own handler */
static void emit_con(Data *D, int ci) {
    Con *C = &cons[D->cons[ci]];
    fprintf(out, "tt_c_%s := ", C->name);
    if (C->bparams) for (int p = 0; p < D->nparams; p++) fprintf(out, "p%d -> ", p);   /* parameters kept when the boundary needs them */
    for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "a%d -> ", j);
    for (int q = 0; q < C->nint; q++) fprintf(out, "i%d -> ", q);
    for (int i = 0; i < nhandlers(D); i++) fprintf(out, "h%d -> ", i);
    fprintf(out, "h%d", ci);
    for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "(a%d)", j);
    for (int q = 0; q < C->nint; q++) fprintf(out, "(i%d)", q);
    fputc('\n', out);
}
/* the formal composition of D: tt_c_D_hcomp phi u u0 selects the last handler */
static void emit_hcomp_con(Data *D) {
    fprintf(out, "tt_c_%s_hcomp := c -> phi -> u -> u0 -> ", D->name);   /* c: the code of its type (parameters and indices) */
    for (int i = 0; i < nhandlers(D); i++) fprintf(out, "h%d -> ", i);
    fprintf(out, "h%d(c)(phi)(u)(u0)\n", D->ncons);
}
/* the q-th index read off a code of D: c(m -> h -> n -> p.. -> i.. -> i_q) */
static void emit_index_of_code(Data *D, int q) {
    fputs("(c(m -> h -> n -> ", out);
    for (int p = 0; p < D->nparams; p++) fprintf(out, "p%d -> ", p);
    for (int j = 0; j < D->nidx; j++) fprintf(out, "i%d -> ", j);
    fprintf(out, "i%d))", q);
}

/* tt_rec_D := fix(rec -> [P ->] m0 -> .. -> x -> x(case_0)..(case_k)[(hcomp case)]); the motive P is taken when hcomp is
   a formal element: the elimination of hcomp phi u u0 is the composition over the motive of the eliminations of the sides,
     comp (k. P (hfill phi u u0 k)) phi [phi -> rec (u k)] (rec u0)                                (the checker's elim_hcomp)
   The eliminators of a block share the prefix [P_0.. (of the members with a formal hcomp), m_0 .. m_{K-1} (every member's
   constructors)]; the eliminator of member m applied to the prefix is emit_rec_call. */
static void emit_rec_call(Data *D, int m) {
    Data *B = &datas[D->block]; int nb = D->nblock, K = block_ncons(D - datas);
    if (nb == 1) fputs("rec", out);
    else { fputs("recs(", out); for (int i = 0; i < nb; i++) fprintf(out, "r%d -> ", i); fprintf(out, "r%d)", m - D->block); }
    for (int i = 0; i < nb; i++) if (formal_hcomp(&B[i])) { if (nb == 1) fputs("(P)", out); else fprintf(out, "(P%d)", i); }
    for (int i = 0; i < K; i++) fprintf(out, "(m%d)", i);
}
static void emit_motive(Data *D) { if (D->nblock == 1) fputs("P", out); else fprintf(out, "P%d", D->bpos); }
/* the body of member D's eliminator: [P.. ->] m.. -> x -> x(case..)[(hcomp case)] */
static void emit_rec_body(Data *D) {
    Data *B = &datas[D->block]; int nb = D->nblock, K = block_ncons(D - datas), hx = formal_hcomp(D);
    for (int i = 0; i < nb; i++) if (formal_hcomp(&B[i])) { if (nb == 1) fputs("P -> ", out); else fprintf(out, "P%d -> ", i); }
    for (int i = 0; i < K; i++) fprintf(out, "m%d -> ", i);
    fputs("x -> x", out);
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fputc('(', out);
        for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "a%d -> ", j);
        for (int q = 0; q < C->nint; q++) fprintf(out, "i%d -> ", q);
        fprintf(out, "m%d", C->bord);
        for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "(a%d)", j);
        for (int j = 0; j < C->nargs; j++) {
            ConArg *A = &C->args[j];
            if (A->isrecpath) {   /* the induction hypothesis over a path argument: k -> rec m.. (a_j k) */
                fputs("(k -> ", out); emit_rec_call(D, A->rec); fprintf(out, "(a%d(k)))", j);
                continue;
            }
            if (!A->isrec) continue;
            /* induction hypothesis: \y_rel.. -> rec m.. (a_j y_rel..) */
            fputc('(', out);
            Term *w = A->ty; int yt = 0;
            for (Term *p = w; p->k == T_PI && yt < A->npi; p = p->b, yt++) if (!p->irr) fprintf(out, "y%d -> ", yt);
            emit_rec_call(D, A->rec);
            fprintf(out, "(a%d", j);
            yt = 0;
            for (Term *p = w; p->k == T_PI && yt < A->npi; p = p->b, yt++) if (!p->irr) fprintf(out, "(y%d)", yt);
            fputs("))", out);
        }
        for (int q = 0; q < C->nint; q++) fprintf(out, "(i%d)", q);
        fputc(')', out);
    }
    if (hx) {   /* the motive at the indices of the composition's type, along the filler */
        fputs("(c -> phi -> u -> u0 -> tt_comp(k -> ", out); emit_motive(D);
        for (int q = 0; q < D->nidx; q++) {
            emit_index_of_code(D, q);
            if (D->idxrec[q] >= 0) { fputc('(', out); emit_rec_call(D, D->idxrec[q]); emit_index_of_code(D, q); fputc(')', out); }   /* its image */
        }
        fputs("(tt_hfill(c)(phi)(u)(u0)(k)))(phi)(k -> tt_sel(phi)(", out); emit_rec_call(D, D - datas);
        fputs("(u(k)))(tt_absurd))(", out); emit_rec_call(D, D - datas); fputs("(u0)))", out);
    }
}
static void emit_rec(Data *D) {
    fprintf(out, "tt_rec_%s := fix(rec -> ", D->name);
    emit_rec_body(D);
    fputs(")\n", out);
}

static void emit_components(Data *D) {   /* p.. -> i.. -> */
    for (int p = 0; p < D->nparams; p++) fprintf(out, "p%d -> ", p);
    for (int j = 0; j < D->nidx; j++) fprintf(out, "i%d -> ", j);
}
/* the line of the j-th argument's type of constructor C at i, given the data line and the fillers of the earlier arguments:
     i -> ((v0 -> .. -> v_{np+j-1} -> A_j')(param_0(line i))..(param_{np-1}(line i))(fl_0(i))..(fl_{j-1}(i)))   */
static void emit_arg_line(Data *D, Con *C, int j) {
    int np = D->nparams;
    fputs("(i -> (", out);
    for (int k = 0; k < np + j; k++) fprintf(out, "v%d -> ", k);
    erase(C->args[j].ty, np + j);
    fputc(')', out);
    for (int k = 0; k < np; k++) {
        fputs("(line(i)(m -> h -> n -> ", out);
        emit_components(D);
        fprintf(out, "p%d))", k);
    }
    for (int k = 0; k < j; k++) fprintf(out, "(fl%d(i))", k);
    fputc(')', out);
}
/* the same at a fixed type: the parameters of the code c */
static void emit_arg_line_at(Data *D, Con *C, int j) {
    int np = D->nparams;
    fputs("(i -> (", out);
    for (int k = 0; k < np + j; k++) fprintf(out, "v%d -> ", k);
    erase(C->args[j].ty, np + j);
    fputc(')', out);
    for (int k = 0; k < np; k++) fprintf(out, "(p%d)", k);
    for (int k = 0; k < j; k++) fprintf(out, "(fl%d(i))", k);
    fputc(')', out);
}
/* the sides of the j-th argument of constructor C: i -> u(i) projected on that argument */
static void emit_sides(Data *D, Con *C, int j) {
    fputs("(i -> u(i)", out);
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *K = &cons[D->cons[ci]];
        fputc('(', out);
        for (int q = 0; q < K->nargs; q++) if (!K->args[q].irr) fprintf(out, "b%d -> ", q);
        if (K == C) fprintf(out, "b%d", j); else fputs("tt_absurd", out);
        fputc(')', out);
    }
    if (formal_hcomp(D)) fputs("(c -> phi -> u -> u0 -> tt_absurd)", out);
    fputc(')', out);
}

/* tc_D := fix(self -> p.. -> k -> k(TRANSP)(HCOMP)(p..)):
     TRANSP := line -> phi -> x -> x(case..)  transports constructor arguments along their own type lines with fillers, exactly
               as the checker does; a formal hcomp transports to the hcomp of the transports;
     HCOMP  := c -> phi -> u -> u0 -> ..     for a formal element builds it; else composes constructor arguments along
               their own type lines with fillers (the checker's structural rule) */
static void emit_code_body(Data *D) {   /* p.. i.. -> k -> k(TRANSP)(HCOMP)(NF)(p..)(i..) */
    int np = D->nparams, m = D->nidx, hx = formal_hcomp(D);
    emit_components(D);
    fputs("k -> k(", out);
    emit_components(D);
    fputs("line -> phi -> x -> x", out);
    self_data = D - datas;
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fputc('(', out);
        for (int j = 0; j < C->nargs; j++) fprintf(out, "a%d -> ", j);
        /* bind the fillers of every argument but the last, in order */
        for (int j = 0; j + 1 < C->nargs; j++) fprintf(out, "(fl%d -> ", j);
        for (int q = 0; q < C->nint; q++) fprintf(out, "i%d -> ", q);
        fprintf(out, "tt_c_%s", C->name);
        if (C->bparams) for (int p = 0; p < np; p++) {   /* parameters kept by the constructor: those of the type at the end of the line */
            fputs("(line(tt_i1)(m -> h -> n -> ", out);
            emit_components(D);
            fprintf(out, "p%d))", p);
        }
        for (int j = 0; j < C->nargs; j++) {
            fputs("(tt_transp", out); emit_arg_line(D, C, j); fprintf(out, "(phi)(a%d))", j);
        }
        for (int q = 0; q < C->nint; q++) fprintf(out, "(i%d)", q);
        for (int j = C->nargs - 2; j >= 0; j--) {
            /* fl_j := i -> transp (k -> A_j(i /\ k)) (phi \/ ~i) a_j */
            fputs(")(i -> tt_transp(k -> ", out); emit_arg_line(D, C, j); fprintf(out, "(tt_iand(i)(k)))(tt_ior(phi)(tt_ineg(i)))(a%d))", j);
        }
        fputc(')', out);
    }
    if (hx)   /* transport of a formal composition: the composition of the transports (the checker's vtransp on a HIT) */
        fputs("(hc -> hphi -> hu -> hu0 -> tt_hcomp(line(tt_i1))(hphi)(i -> tt_transp(line)(phi)(hu(i)))(tt_transp(line)(phi)(hu0)))", out);
    fputs(")(", out);
    emit_components(D);
    fputs("c -> phi -> u -> u0 -> ", out);
    if (hx) { fprintf(out, "tt_c_%s_hcomp(c)(phi)(u)(u0)", D->name); }
    else {
        fputs("u0", out);
        for (int ci = 0; ci < D->ncons; ci++) {
            Con *C = &cons[D->cons[ci]];
            fputc('(', out);
            for (int j = 0; j < C->nargs; j++) fprintf(out, "a%d -> ", j);
            for (int j = 0; j + 1 < C->nargs; j++) fprintf(out, "(fl%d -> ", j);
            fprintf(out, "tt_c_%s", C->name);
            for (int j = 0; j < C->nargs; j++) {
                fputs("(tt_comp", out); emit_arg_line_at(D, C, j); fputs("(phi)", out); emit_sides(D, C, j); fprintf(out, "(a%d))", j);
            }
            for (int j = C->nargs - 2; j >= 0; j--) {
                /* fl_j := fill of the composition of a_j along its line */
                fputs(")(tt_fill", out); emit_arg_line_at(D, C, j); fputs("(phi)", out); emit_sides(D, C, j); fprintf(out, "(a%d))", j);
            }
            fputc(')', out);
        }
    }
    /* NF := p.. i.. -> c -> x -> x(case..): constructor arguments normalized at their own types, path constructors at
       endpoints reduced through their boundary (the boundary's elements normalized), formal compositions kept */
    fputs(")(", out);
    emit_components(D);
    fputs("c -> x -> x", out);
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        int r = C->nargs;
        fputc('(', out);
        for (int j = 0; j < r; j++) fprintf(out, "a%d -> ", j);
        for (int q = 0; q < C->nint; q++) fprintf(out, "i%d -> ", q);
        if (C->nint > 0 && C->boundary) {   /* ((v.. -> tt_sel(face)(nf body)..(the constructor))(p..)(a..)(i..)) */
            fputs("((", out);
            for (int k = 0; k < np + r + C->nint; k++) fprintf(out, "v%d -> ", k);
            for (int b = 0; b < C->boundary->nbr; b++) { fputs("tt_sel(", out); erase_face(C->boundary->br[b].face, np + r + C->nint); fputs(")(tt_nf(c)(", out); erase(C->boundary->br[b].body, np + r + C->nint); fputs("))(", out); }
            fprintf(out, "tt_c_%s", C->name);
            if (C->bparams) for (int p = 0; p < np; p++) fprintf(out, "(v%d)", p);
            for (int j = 0; j < r; j++) fprintf(out, "(v%d)", np + j);
            for (int q = 0; q < C->nint; q++) fprintf(out, "(v%d)", np + r + q);
            for (int b = 0; b < C->boundary->nbr; b++) fputc(')', out);
            fputc(')', out);
            for (int p = 0; p < np; p++) fprintf(out, "(p%d)", p);
            for (int j = 0; j < r; j++) fprintf(out, "(a%d)", j);
            for (int q = 0; q < C->nint; q++) fprintf(out, "(i%d)", q);
            fputc(')', out);
        } else {
            fprintf(out, "tt_c_%s", C->name);
            if (C->bparams) for (int p = 0; p < np; p++) fprintf(out, "(p%d)", p);
            for (int j = 0; j < r; j++) {   /* nf of a_j at its type: ((v.. -> A_j)(p..)(a_0..a_{j-1})) */
                fputs("(tt_nf((", out);
                for (int k = 0; k < np + j; k++) fprintf(out, "v%d -> ", k);
                erase(C->args[j].ty, np + j);
                fputc(')', out);
                for (int p = 0; p < np; p++) fprintf(out, "(p%d)", p);
                for (int k = 0; k < j; k++) fprintf(out, "(a%d)", k);
                fprintf(out, ")(a%d))", j);
            }
            for (int q = 0; q < C->nint; q++) fprintf(out, "(i%d)", q);
        }
        fputc(')', out);
    }
    /* a printed value holds no functions (their combinator normal forms are not canonical): the code and the tube of a
       closed formal composition are placeholders — its face is i0 and the tube is never consulted — and its base is normalized */
    if (hx) fprintf(out, "(hc -> hphi -> hu -> hu0 -> tt_c_%s_hcomp(tt_absurd)(hphi)(tt_absurd)(tt_nf(c)(hu0)))", D->name);
    self_data = -1;
    fputc(')', out);
    for (int p = 0; p < np; p++) fprintf(out, "(p%d)", p);
    for (int j = 0; j < m; j++) fprintf(out, "(i%d)", j);
}
static void emit_codes(Data *D) {
    fprintf(out, "tc_%s := fix(self -> ", D->name);
    emit_code_body(D);
    fputs(")\n", out);
}
/* a block of several: the codes as one fixpoint over a tuple (the members' codes refer to each other), then each member's
   code as a selection; likewise the eliminators */
static void emit_block_codes(Data *B) {
    int nb = B->nblock;
    fprintf(out, "tcb_%s := fix(selfs -> k -> k", B->name);
    for (int i = 0; i < nb; i++) { fputc('(', out); emit_code_body(&B[i]); fputc(')', out); }
    fputs(")\n", out);
    for (int i = 0; i < nb; i++) { fprintf(out, "tc_%s := tcb_%s(", B[i].name, B->name); emit_sel(nb, i); fputs(")\n", out); }
}
static void emit_block_recs(Data *B) {
    int nb = B->nblock;
    fprintf(out, "ttrecs_%s := fix(recs -> k -> k", B->name);
    for (int i = 0; i < nb; i++) { fputc('(', out); emit_rec_body(&B[i]); fputc(')', out); }
    fputs(")\n", out);
    for (int i = 0; i < nb; i++) { fprintf(out, "tt_rec_%s := ttrecs_%s(", B[i].name, B->name); emit_sel(nb, i); fputs(")\n", out); }
}

/* Only what main reaches is emitted, and each declaration after what its erasure refers to: eezoc expands a
   definition at every reference, so a definition must stand before its uses, and the order of declaration is not
   that order once the Nat's representation (declared last, in num.tt) is what every earlier fold's suc and elim
   erase to. So the emission is a depth-first walk from main: a definition's body is walked first, every
   definition and data type it reaches is emitted, then the definition itself; a data type's block is emitted
   whole (constructors, codes, eliminators) after the types its constructors mention, and refers to itself freely. */
/* the run-time Glue layer: emitted right after the prelude's equivProof, which its transport rule calls */
static void emit_glue_runtime(void) {
    /* Glue: an element is the glued element itself where phi holds, and otherwise the pair (sides, base) */
    fputs("tt_glue := phi -> ts -> a -> tt_sel(phi)(ts)(tt_pair(ts)(a))\n", out);
    fputs("tt_unglue := phi -> te -> b -> tt_sel(phi)(tt_fst(tt_snd(te))(b))(tt_snd(b))\n", out);
    fputs("tt_gA := c -> c(m -> h -> n -> a -> phi -> te -> a)\n", out);
    fputs("tt_gphi := c -> c(m -> h -> n -> a -> phi -> te -> phi)\n", out);
    fputs("tt_gte := c -> c(m -> h -> n -> a -> phi -> te -> te)\n", out);
    fputs("tt_gcomp := line -> phi -> u -> u0 -> tt_hcomp(line(tt_i1))(tt_ior(phi)(tt_ineg(phi)))(i -> tt_sel(phi)(tt_transp(j -> line(tt_ior(i)(j)))(i)(u(i)))(tt_transp(line)(tt_i0)(u0)))(tt_transp(line)(tt_i0)(u0))\n", out);
    /* transport along a line of Glue types, as in the checker, including the face "forall i. phi" on which the glued
       types form a line along i: tt_forall evaluates the line's face at half, and a face is 1 in the free De Morgan
       algebra exactly when it is 1 at half. */
    fputs("tt_transp_glue := a -> phi -> te -> line -> psi -> u0 -> "
          "(fa -> (ungl -> (tf -> (a1 -> (phi1 -> (te1 -> "
          "(fib -> tt_glue(phi1)(tt_fst(fib))(tt_hcomp(tt_gA(line(tt_i1)))(tt_ior(phi1)(psi))(j -> tt_sel(phi1)(tt_snd(fib)(tt_ineg(j)))(a1))(a1)))"
          "(tt_equivProof(tt_fst(te1))(tt_gA(line(tt_i1)))(tt_snd(te1))(a1)(tt_ior(psi)(fa))"
          "(tt_sel(psi)(tt_pair(u0)(j -> a1))(tt_sel(fa)(tt_pair(tf(tt_i1))(j -> a1))(tt_absurd)))))"
          "(tt_gte(line(tt_i1))))(tt_gphi(line(tt_i1))))"
          "(tt_gcomp(i -> tt_gA(line(i)))(tt_ior(psi)(fa))(i -> tt_sel(psi)(ungl(i))(tt_sel(fa)(tt_fst(tt_snd(tt_gte(line(i))))(tf(i)))(tt_absurd)))(ungl(tt_i0))))"
          "(i -> tt_transp(j -> tt_fst(tt_gte(line(tt_iand(i)(j)))))(tt_ior(psi)(tt_ineg(i)))(u0)))"
          "(i -> tt_unglue(tt_gphi(line(i)))(tt_gte(line(i)))(u0)))"
          "(tt_forall(i -> tt_gphi(line(i))))\n", out);
    /* hcomp in a Glue type, as in the checker (hcomp_glue): compose in T on phi (a filler tf), compose in A on psi \/ phi
       with the unglued sides and e.1 of the filler on phi, and glue the filler's end over the result */
    fputs("tt_hc_glue := a -> phi -> te -> c -> psi -> u -> u0 -> (tf -> tt_glue(phi)(tf(tt_i1))"
          "(tt_hcomp(a)(tt_ior(psi)(phi))(i -> tt_sel(psi)(tt_unglue(phi)(te)(u(i)))(tt_sel(phi)(tt_fst(tt_snd(te))(tf(i)))(tt_absurd)))"
          "(tt_unglue(phi)(te)(u0))))(k -> tt_hfill(tt_fst(te))(psi)(u)(u0)(k))\n", out);
    fputs("tt_nf_glue := a -> phi -> te -> c -> x -> x\n", out);
    fputs("tc_glue := a -> phi -> te -> k -> k(tt_transp_glue)(tt_hc_glue)(tt_nf_glue)(a)(phi)(te)\n", out);
}

static void emit_def(int d) {
    if (def_state[d] == 2) return;
    if (def_state[d] == 1) die("internal: the definitions %s reach themselves at run time", defs[d].name);
    def_state[d] = 1;
    const char *outer = cur_decl_name; cur_decl_name = defs[d].name;
    visit(defs[d].val);
    cur_decl_name = defs[d].name;   /* erasure unfolds redexes, and an inductive lemma at a literal walks it */
    fprintf(out, "tt_%s := ", defs[d].name); erase(defs[d].val, 0); fputc('\n', out);
    if (!strcmp(defs[d].name, "equivProof")) emit_glue_runtime();
    if (!strcmp(defs[d].name, "transpEquiv"))   /* hcomp in the universe: the Glue type of the lid glued along transport back down the sides */
        fputs("tt_hcompU := phi -> u -> u0 -> tc_glue(u0)(phi)(tt_sel(phi)(tt_pair(u(tt_i1))(tt_transpEquiv(i -> u(tt_ineg(i)))))(tt_absurd))\n", out);
    def_state[d] = 2; cur_decl_name = outer;
}
static void emit_block(int d) {
    Data *B = &datas[datas[d].block]; int b = B - datas, nb = B->nblock;
    if (data_state[b]) return;   /* emitted, or being emitted: a recursive occurrence refers to the block's own self */
    data_state[b] = 1;
    for (int i = 0; i < nb; i++) { visit(B[i].ty); for (int ci = 0; ci < B[i].ncons; ci++) { visit(cons[B[i].cons[ci]].ty); visit(cons[B[i].cons[ci]].boundary); } }   /* a path constructor's boundary is erased with its code */
    if (nb > 1) {   /* a mutual block, emitted as a whole */
        for (int i = 0; i < nb; i++) { for (int ci = 0; ci < B[i].ncons; ci++) emit_con(&B[i], ci); if (formal_hcomp(&B[i])) emit_hcomp_con(&B[i]); }
        emit_block_codes(B);
        emit_block_recs(B);
    } else {
        for (int ci = 0; ci < B->ncons; ci++) emit_con(B, ci);
        if (formal_hcomp(B)) emit_hcomp_con(B);
        emit_codes(B);
        emit_rec(B);
    }
    data_state[b] = 2;
}
static void visit(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF:
        if (defs[t->n].native) {   /* the representation's operation stands for it; without a law, its body */
            Rep *r = rep_of(native_dom(t->n));
            if (r && r->native[defs[t->n].native]) { visit(r->native[defs[t->n].native]); break; }
        }
        if (defs[t->n].wordop || defs[t->n].isword) break;   /* the primitive stands for it: its body is not emitted */
        emit_def(t->n);
        break;
    case T_NUM: { Rep *r = rep_of(t->n);
        if (r) { if (r->npos) { visit(r->zero); visit(r->npos); visit(r->cons); visit(r->top); } else visit(literal_via_map(r, t)); break; }
        visit(numeral_term(t->n, t->a, t->num)); break; }
    case T_PAIR: if (t->n && t->a->k != T_NUM) visit(role_need(rep_need(word_nat, "a word from a value")->low, "a value's low word")); visit(t->a); if (!t->irr) visit(t->b); break;
    case T_FST: if (t->n) visit(role_need(rep_need(word_nat, "a word's value")->single, "a word's value")); visit(t->a); break;
    case T_SIGMA: visit(t->a); if (!t->irr) visit(t->b); break;
    case T_SND: visit(t->a); break;
    case T_CON: { Rep *r = rep_of(cons[t->n].data); if (r) { visit(role_need(cons[t->n].nargs == 0 ? r->zero : r->suc, cons[t->n].name)); break; } emit_block(cons[t->n].data); break; }
    case T_ELIM: { Rep *r = rep_of(t->n); if (r) { visit(role_need(r->isz, "an elimination's zero test")); visit(role_need(r->pred, "an elimination's predecessor")); break; } emit_block(t->n); break; }
    case T_DATA: { Rep *r = rep_of(t->n); if (r) { visit(r->R); break; } emit_block(t->n); break; }
    case T_SYS: for (int i = 0; i < t->nbr; i++) { visit(t->br[i].face); visit(t->br[i].body); } break;
    case T_APP: if (nat_elim_spine(t, 0, 0)) break; visit(t->a); if (!t->irr) visit(t->b); break;   /* a Nat elimination's spine: what its erasure refers to */
    case T_TRANSP: if (keep_kan || !(t->n || t->b->k == T_I1)) { visit(t->a); visit(t->b); } visit(t->c); break;
    case T_HCOMP: visit(t->a); visit(t->b); visit(t->c); visit(t->d);
        if (t->n) for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "transpEquiv") || !strcmp(defs[i].name, "equivProof")) emit_def(i);
        break;
    case T_GLUE: visit(t->a); visit(t->b); visit(t->c);
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "equivProof")) emit_def(i);
        break;
    default: visit(t->a); visit(t->b); visit(t->c); visit(t->d); break;
    }
}

/* ---- the representations: the equivalence in scope, and each role by the shape of its law ---- */
static Term *tvar(int i) { return mk_var(i); }
static Term *tref(TKind k, int id) { return mk_ref_l(k, id, mk_lval(lv_const(0))); }
static Term *tapp(Term *f, Term *a) { return mk_app(f, a, 0); }
static int newm(void) { return meta_new(vu(0), 0, NULL, 0); }
static Term *tm(int id) { return meta_term(id, 0); }
static Term *tpath(Term *A, Term *x, Term *y) { Term *line = mk_lam("_", shift(A, 0, 1), 0); line->isi = 1; return mk_term(T_PATHP, line, x, y, NULL); }
static Term *tpi(Term *A, Term *B) { return mk_pi("y", A, B, 0); }
static Term *tfst(Term *a) { return mk_term(T_FST, a, NULL, NULL, NULL); }
static Term *tsnd(Term *a) { return mk_term(T_SND, a, NULL, NULL, NULL); }
static Term *tlam(Term *body) { return mk_lam("y", body, 0); }
/* \x -> f x is f: a solution read as the implementation it names */
static Term *eta_strip(Term *t) {
    while (t && t->k == T_LAM && !t->irr && t->a->k == T_APP && !t->a->irr && t->a->b->k == T_VAR && t->a->b->n == 0 && !term_mentions_var(t->a->a, 0))
        t = shift(t->a->a, 0, -1);
    return t;
}
/* Unify a pattern type (closed, with the nm metas m0.. minted for it) against the type of every definition in scope: the
   number of definitions that have its shape; for the last of them, the definition and the metas' solutions (every meta
   must be solved, postponed constraints retried). Every attempt is rolled back, so the metas are fresh for the next. */
typedef struct { int def, def2; Term *sol[8]; } Match;
/* a definition's type has the pattern's shape: as many leading binders, none an interval where the pattern's is not, and the
   same form after them (a path, or the equivalence). conv is asked only then: on types of another shape it can die rather
   than fail - a projection on an interval variable, say - and it would waste its time */
static int shape_ok(Val *ty, Term *pat, int equiv_def) {
    int i = 0;
    for (Term *p = pat; p->k == T_PI; p = p->b, i++) {
        Val *t = fmeta(ty); if (t->k != V_PI) t = force(ty);   /* as written; through a definition only when it is one */
        if (t->k != V_PI || t->isi != p->isi) return 0;
        ty = inst(&t->clo, p->isi ? vivar(i) : vvar(i));
    }
    Term *end = pat; while (end->k == T_PI) end = end->b;
    Val *t = fmeta(ty);
    if (end->k == T_PATHP) { if (t->k != V_PATHP) t = force(ty); return t->k == V_PATHP; }
    if (t->k == V_NEU && t->h == H_DEF && t->n == equiv_def) return 1;   /* the equivalence, as written */
    return force(ty)->k == V_SIGMA;                                      /* or spelled out: conv decides */
}
static int the_equiv_def = -1;
static int match_laws(Term *pat, int m0, int nm, Match *m) {
    Val *pv = eval(NULL, pat); int hits = 0; m->def = m->def2 = -1;
    for (int i = 0; i < ndefs; i++) {
        if (!shape_ok(defs[i].vty, pat, the_equiv_def)) continue;
        MMark mk = meta_mark();
        int c1 = conv(0, defs[i].vty, pv), c2 = c1 ? metas_retry() : 0, ok = c1 && c2;
        for (int k = 0; ok && k < nm; k++) if (!meta_solved(m0 + k)) ok = 0;
        if (ok) { hits++; m->def2 = m->def; m->def = i; for (int k = 0; k < nm; k++) m->sol[k] = eta_strip(zonk(tmetas[m0 + k].solt)); }
        meta_rollback(mk);
    }
    return hits;
}
/* the one law of a role: its solutions in sols; NULL when there is none (dies if must), refused when there are two */
static int find_role(const char *what, Term *pat, int m0, int nm, int must, Term **sols) {
    Match m; int n = match_laws(pat, m0, nm, &m);
    if (rep_trace < 0) rep_trace = getenv("EEZOTT_REP_TRACE") != NULL;
    if (rep_trace) fprintf(stderr, "[rep] %s: %d law(s)%s%s\n", what, n, n ? " e.g. " : "", n ? defs[m.def].name : "");
    if (n > 1) die("the run-time representation's law for %s is ambiguous: %s and %s both have its shape", what, defs[m.def2].name, defs[m.def].name);
    if (n == 0) { if (must) die("the run-time representation has no law for %s", what); return 0; }
    for (int k = 0; k < nm; k++) sols[k] = m.sol[k];
    return 1;
}
/* the solution v of a left side fst (L y): L, read off the value of v y - a neutral whose last spine entry is the projection */
static Term *peel_fst(Term *v, const char *what) {
    Val *x = force(vapp(eval(NULL, v), vvar(0), 0));
    if (x->k != V_NEU || x->args.n == 0 || x->args.a[x->args.n - 1].proj != 1) die("the law for %s must read the first component of the operation's result", what);
    Val *w = mkval(V_NEU); *w = *x; w->args.n--;
    return eta_strip(mk_lam("y", quote(1, w), 0));
}
static Term *m64_literal(int d) { return mk_num(d, NULL, bn_from_dec("18446744073709551616")); }
/* pred, as the eliminator: elim d (\_ -> d) zero (\k _ -> k) x */
static Term *tpred(Rep *r, Term *x) {
    Term *D = tref(T_DATA, r->d);
    Term *e = tref(T_ELIM, r->d);
    e = tapp(e, mk_lam("_", D, 0));
    e = tapp(e, tref(T_CON, r->zi));
    e = tapp(e, mk_lam("k", mk_lam("_", mk_var(1), 0), 0));
    return tapp(e, x);
}
static void find_representation(int d, int zi, int si, int equiv_def) {
    Term *D = tref(T_DATA, d), *sols[8];
    int mR = newm();
    Match m; int n = match_laws(tapp(tapp(tref(T_DEF, equiv_def), D), tm(mR)), mR, 1, &m);
    if (n == 0) return;   /* no equivalence in scope: the type runs as itself */
    if (n > 1) die("%s has two run-time representations in scope, %s and %s: one is needed", datas[d].name, defs[m.def2].name, defs[m.def].name);
    reps = realloc(reps, (nreps + 1) * sizeof(Rep)); if (!reps) die_resource("out of memory");
    Rep *r = &reps[nreps++]; memset(r, 0, sizeof *r);
    r->d = d; r->zi = zi; r->si = si; r->equiv = m.def; r->R = m.sol[0];
    /* the successor's law binds the value map g: (y : R) -> Path d (g (s y)) (suc (g y)) */
    int mg = newm(), ms = newm();
    find_role("the successor", tpi(r->R, tpath(D, tapp(tm(mg), tapp(tm(ms), tvar(0))), tapp(tref(T_CON, si), tapp(tm(mg), tvar(0))))), mg, 2, 1, sols);
    r->g = sols[0]; r->suc = sols[1];
    /* and g must be the equivalence's inverse: the centre of its fibres, y -> fst (fst (snd e y)) */
    Term *centre = tlam(tfst(tfst(tapp(tsnd(tref(T_DEF, r->equiv)), tvar(0)))));
    if (!conv(0, eval(NULL, r->g), eval(NULL, centre)))
        die("the laws of %s's run-time representation are stated with a value map that is not the inverse of the equivalence %s", datas[d].name, defs[r->equiv].name);
    /* zero: Path d (g z) zero */
    int mz = newm();
    find_role("zero", tpath(D, tapp(r->g, tm(mz)), tref(T_CON, zi)), mz, 1, 1, sols); r->zero = sols[0];
    /* the zero test: (y : R) -> Path B (i y) true -> Path d (g y) zero, B a data type of two nullary constructors, true its first */
    int mB = newm(), mI = newm(), mT = newm();
    find_role("the zero test", tpi(r->R, mk_pi("_", tpath(tm(mB), tapp(tm(mI), tvar(0)), tm(mT)), tpath(D, tapp(r->g, tvar(1)), tref(T_CON, zi)), 0)), mB, 3, 1, sols);
    { Term *B = sols[0], *T = sols[2];
      int ok = B->k == T_DATA && datas[B->n].ncons == 2 && cons[datas[B->n].cons[0]].nargs == 0 && cons[datas[B->n].cons[1]].nargs == 0
               && T->k == T_CON && T->n == datas[B->n].cons[0];
      if (!ok) die("the zero test's law of %s's representation does not answer in a type of two nullary constructors with its first as true", datas[d].name); }
    r->isz = sols[1];
    /* the predecessor: (y : R) -> Path d (g (p y)) (pred (g y)) */
    int mp = newm();
    find_role("the predecessor", tpi(r->R, tpath(D, tapp(r->g, tapp(tm(mp), tvar(0))), tpred(r, tapp(r->g, tvar(0))))), mp, 1, 1, sols); r->pred = sols[0];
    /* the word boundary and the digits need the word type */
    if (word_type >= 0 && word_nat == d) {
        Term *W = tref(T_DEF, word_type);
        int msg = newm();
        if (find_role("a word's value", tpi(W, tpath(D, tapp(r->g, tapp(tm(msg), tvar(0))), tfst(tvar(0)))), msg, 1, 0, sols)) r->single = sols[0];
        int modd = native_of(d, NR_MOD);
        if (modd >= 0) {   /* (y : R) -> Path d (fst (lo y)) (mod (g y) 2^64): fst (lo y) is no pattern, so the left side is bound whole and lo peeled off it */
            int mv = newm();
            if (find_role("a value's low word", tpi(r->R, tpath(D, tapp(tm(mv), tvar(0)), tapp(tapp(tref(T_DEF, modd), tapp(r->g, tvar(0))), m64_literal(d)))), mv, 1, 0, sols))
                r->low = peel_fst(sols[0], "a value's low word");
        }
    }
    /* the natives: (x y : R) -> Path d (g (h x y)) (f (g x) (g y)), or answering in d itself: Path d (h x y) (f (g x) (g y)) */
    for (int code = 1; code < NR_COUNT; code++) {
        int f = native_of(d, code); if (f < 0) continue;
        Term *rhs = tapp(tapp(tref(T_DEF, f), tapp(r->g, tvar(1))), tapp(r->g, tvar(0)));
        int mh = newm(); Match a, b;
        int na = match_laws(tpi(r->R, tpi(r->R, tpath(D, tapp(r->g, tapp(tapp(tm(mh), tvar(1)), tvar(0))), rhs))), mh, 1, &a);
        if (na > 1) die("the run-time representation's law for %s is ambiguous: %s and %s both have its shape", defs[f].name, defs[a.def2].name, defs[a.def].name);
        if (na == 1) { r->native[code] = a.sol[0]; r->native_direct[code] = 0; continue; }
        int mh2 = newm();   /* answering in d itself (a decision): h x y matches any left side, so only when the value form has none */
        int nb = match_laws(tpi(r->R, tpi(r->R, tpath(D, tapp(tapp(tm(mh2), tvar(1)), tvar(0)), rhs))), mh2, 1, &b);
        if (nb > 1) die("the run-time representation's law for %s is ambiguous: %s and %s both have its shape", defs[f].name, defs[b.def2].name, defs[b.def].name);
        if (nb == 1) { r->native[code] = b.sol[0]; r->native_direct[code] = 1; }
    }
    /* the digits, in the order that pins them: a word under a numeral (l : Word) (p : P) -> Path d (gP (cons l p)) (add (fst l) (mul (gP p) 2^64))
       binds the positive type P and its value map gP; then the top word (w : W) -> Path d (gP (top w)) (fst (fst w)), W a pair type over the
       word with an irrelevant second; then the injection (p : P) -> Path d (g (npos p)) (gP p) */
    if (word_type >= 0 && word_nat == d) {
        int addd = native_of(d, NR_ADD), muld = native_of(d, NR_MUL);
        if (addd >= 0 && muld >= 0) {
            Term *W = tref(T_DEF, word_type);
            int mP = newm(), mgP = newm(), mc = newm();
            if (find_role("a word under a numeral", tpi(W, tpi(tm(mP), tpath(D, tapp(tm(mgP), tapp(tapp(tm(mc), tvar(1)), tvar(0))),
                    tapp(tapp(tref(T_DEF, addd), tfst(tvar(1))), tapp(tapp(tref(T_DEF, muld), tapp(tm(mgP), tvar(0))), m64_literal(d)))))), mP, 3, 0, sols)) {
                r->P = sols[0]; r->gP = sols[1]; r->cons = sols[2];
                int mq = newm(), mt = newm();
                Term *pw = mk_term(T_SIGMA, W, tapp(tm(mq), tvar(0)), NULL, NULL); pw->name = "w"; pw->irr = 1;
                find_role("the top word of a numeral", tpi(pw, tpath(D, tapp(r->gP, tapp(tm(mt), tvar(0))), tfst(tfst(tvar(0))))), mq, 2, 1, sols);
                r->top = sols[1];
                int mnp = newm();
                find_role("the injection of a numeral", tpi(r->P, tpath(D, tapp(r->g, tapp(tm(mnp), tvar(0))), tapp(r->gP, tvar(0)))), mnp, 1, 1, sols);
                r->npos = sols[0];
            }
        }
    }
}
static void find_representations(void) {
    int equiv_def = def_named("Equiv");
    if (equiv_def < 0) return;
    the_equiv_def = equiv_def;
    for (int d = 0; d < ndatas; d++) { int zi, si; if (peano_shape(d, &zi, &si)) find_representation(d, zi, si, equiv_def); }
}
/* a literal of a represented type: its machine words low word first through the digit roles, or, without digit laws,
   the equivalence's forward map applied to it by the checker and the value quoted */
static Term *literal_via_map(Rep *r, Term *t) {
    Val *f = vproj(defs[r->equiv].vval, 1);
    return quote(0, nf_force(vapp(f, vnum(r->d, lv_const(0), t->num), 0)));
}
static void erase_literal(Rep *r, Term *t, int depth) {
    if (!r->npos) { erase(literal_via_map(r, t), depth); return; }
    int n = t->num->n;
    if (n == 0) { erase(r->zero, depth); return; }
    erase(r->npos, depth); fputc('(', out);
    for (int i = 0; i + 1 < n; i++) { erase(r->cons, depth); fprintf(out, "(%lluw)(", (unsigned long long)t->num->limb[i]); }
    erase(r->top, depth); fprintf(out, "(%lluw)", (unsigned long long)t->num->limb[n - 1]);
    for (int i = 0; i + 1 < n; i++) fputc(')', out);
    fputc(')', out);
}

void erase_program(FILE *f) {
    char *buf = NULL; size_t sz = 0;
    out = open_memstream(&buf, &sz);
    int mainid = -1;
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "main")) mainid = i;
    if (mainid < 0) die("no 'main' definition to run");
    if (defs[mainid].irr) die("'main' is a type; a program must be a value");
    if (nf_main) defs[mainid].val = quote(0, nf_force(defs[mainid].vval));   /* the checker's normal form instead of the source (rigid: definitions are opaque values) */
    def_state = xalloc((ndefs + 1) * sizeof(int)); data_state = xalloc((ndatas + 1) * sizeof(int));
    find_representations();
    fputs("#import prelude\n", out);
    /* the interval as three-valued Scott data (i0, half, i1) with Kleene's tables; a closed face is i0 or i1 and
       selects (tt_sel: 1 -> x, 0 -> y); half is the symbol of tt_forall. Then the run-time meaning of systems,
       hcomp, transport and the codes of the basic type formers. */
    fputs("tt_absurd := x -> x\n", out);
    fputs("tt_i0 := z -> h -> o -> z\n", out);
    fputs("tt_ihalf := z -> h -> o -> h\n", out);
    fputs("tt_i1 := z -> h -> o -> o\n", out);
    fputs("tt_iand := x -> y -> x(tt_i0)(y(tt_i0)(tt_ihalf)(tt_ihalf))(y)\n", out);
    fputs("tt_ior := x -> y -> x(y)(y(tt_ihalf)(tt_ihalf)(tt_i1))(tt_i1)\n", out);
    fputs("tt_ineg := x -> x(tt_i1)(tt_ihalf)(tt_i0)\n", out);
    fputs("tt_sel := phi -> x -> y -> phi(y)(tt_absurd)(x)\n", out);
    fputs("tt_forall := f -> f(tt_ihalf)(tt_i0)(tt_i0)(tt_i1)\n", out);
    /* a code is k -> k(transport rule)(hcomp rule)(components); hcomp at phi = 1 is the side at i1, else the code's rule */
    fputs("tt_hcomp := c -> phi -> u -> u0 -> tt_sel(phi)(u(tt_i1))(c(m -> h -> n -> h)(c)(phi)(u)(u0))\n", out);
    fputs("tt_transp := line -> phi -> a -> tt_sel(phi)(a)(line(tt_i0)(m -> h -> n -> m)(line)(phi)(a))\n", out);
    fputs("tt_comp := line -> phi -> u -> u0 -> tt_hcomp(line(tt_i1))(phi)(i -> tt_transp(j -> line(tt_ior(i)(j)))(i)(u(i)))(tt_transp(line)(tt_i0)(u0))\n", out);
    fputs("tt_hfill := c -> phi -> u -> u0 -> k -> tt_hcomp(c)(tt_ior(phi)(tt_ineg(k)))(i -> tt_sel(phi)(u(tt_iand(i)(k)))(tt_sel(tt_ineg(k))(u0)(tt_absurd)))(u0)\n", out);
    fputs("tt_fill := line -> phi -> u -> u0 -> i -> tt_comp(j -> line(tt_iand(i)(j)))(tt_ior(phi)(tt_ineg(i)))(j -> tt_sel(phi)(u(tt_iand(i)(j)))(tt_sel(tt_ineg(i))(u0)(tt_absurd)))(u0)\n", out);
    fputs("tt_hc_id := c -> phi -> u -> u0 -> u0\n", out);
    fputs("tt_transp_u := line -> phi -> a -> a\n", out);
    /* the printed value: a normalizer per code (tt_nf c x); data types reduce path constructors at endpoints through their
       boundaries and keep formal compositions; functions are printed as they are */
    fputs("tt_nf := c -> x -> c(m -> h -> n -> n)(c)(x)\n", out);
    fputs("tt_nf_id := c -> x -> x\n", out);
    fputs("tc_u := k -> k(tt_transp_u)(tt_hc_id)(tt_nf_id)\n", out);
    fputs("tt_dom := c -> c(m -> h -> n -> d -> b -> d)\n", out);
    fputs("tt_cod := c -> c(m -> h -> n -> d -> b -> b)\n", out);
    fputs("tt_hc_pi := d -> b -> c -> phi -> u -> u0 -> x -> tt_hcomp(b(x))(phi)(i -> u(i)(x))(u0(x))\n", out);
    fputs("tt_transp_pi := d -> b -> line -> phi -> f -> x -> (v -> tt_transp(i -> tt_cod(line(i))(v(i)))(phi)(f(v(tt_i0))))"
          "(i -> tt_transp(j -> tt_dom(line(tt_ior(i)(tt_ineg(j)))))(tt_ior(phi)(i))(x))\n", out);
    fputs("tt_nf_pi := d -> b -> c -> x -> x\n", out);
    fputs("tc_pi := d -> b -> k -> k(tt_transp_pi)(tt_hc_pi)(tt_nf_pi)(d)(b)\n", out);
    fputs("tt_pline := c -> c(m -> h -> n -> l -> x -> y -> l)\n", out);
    fputs("tt_px := c -> c(m -> h -> n -> l -> x -> y -> x)\n", out);
    fputs("tt_py := c -> c(m -> h -> n -> l -> x -> y -> y)\n", out);
    fputs("tt_hc_path := l -> x -> y -> c -> phi -> u -> u0 -> j -> tt_hcomp(l(j))(tt_ior(phi)(tt_ior(j)(tt_ineg(j))))"
          "(i -> tt_sel(phi)(u(i)(j))(tt_sel(tt_ineg(j))(x)(tt_sel(j)(y)(tt_absurd))))(u0(j))\n", out);
    fputs("tt_transp_path := l -> x -> y -> line -> phi -> p -> j -> tt_comp(i -> tt_pline(line(i))(j))(tt_ior(phi)(tt_ior(j)(tt_ineg(j))))"
          "(i -> tt_sel(phi)(p(j))(tt_sel(tt_ineg(j))(tt_px(line(i)))(tt_sel(j)(tt_py(line(i)))(tt_absurd))))(p(j))\n", out);
    fputs("tt_nf_path := l -> x -> y -> c -> p -> p\n", out);
    fputs("tc_path := l -> x -> y -> k -> k(tt_transp_path)(tt_hc_path)(tt_nf_path)(l)(x)(y)\n", out);
    fputs("tt_pair := a -> b -> k -> k(a)(b)\n", out);
    fputs("tt_fst := p -> p(a -> b -> a)\n", out);
    fputs("tt_snd := p -> p(a -> b -> b)\n", out);
    fputs("tt_transp_sigma := d -> b -> line -> phi -> p -> tt_pair(tt_transp(i -> tt_dom(line(i)))(phi)(tt_fst(p)))"
          "(tt_transp(i -> tt_cod(line(i))(tt_transp(j -> tt_dom(line(tt_iand(i)(j))))(tt_ior(phi)(tt_ineg(i)))(tt_fst(p))))(phi)(tt_snd(p)))\n", out);
    fputs("tt_hc_sigma := d -> b -> c -> phi -> u -> u0 -> tt_pair(tt_hcomp(d)(phi)(i -> tt_fst(u(i)))(tt_fst(u0)))"
          "(tt_comp(i -> b(tt_hfill(d)(phi)(j -> tt_fst(u(j)))(tt_fst(u0))(i)))(phi)(i -> tt_snd(u(i)))(tt_snd(u0)))\n", out);
    fputs("tt_nf_sigma := d -> b -> c -> x -> tt_pair(tt_nf(d)(tt_fst(x)))(tt_nf(b(tt_fst(x)))(tt_snd(x)))\n", out);
    fputs("tc_sigma := d -> b -> k -> k(tt_transp_sigma)(tt_hc_sigma)(tt_nf_sigma)(d)(b)\n", out);
    emit_def(mainid);
    visit(defs[mainid].ty);   /* the normalizer's code, at the end */
    fclose(out);
    /* eezoc reads `defs ; expr`: the separator must follow the last definition on its line */
    if (sz && buf[sz - 1] == '\n') buf[sz - 1] = 0;
    fprintf(f, "%s;\ntt_nf(", buf); out = f; erase(defs[mainid].ty, 0); fprintf(f, ")(tt_%s)\n", defs[mainid].name);
    free(buf);
}
