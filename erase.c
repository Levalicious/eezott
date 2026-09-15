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
static FILE *out;
static int self_data = -1;      /* while emitting tc_D: references to D are the fixpoint's self */
static void emit_sel(int nb, int m);

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
        erase(t->a, depth);
        if (!t->irr) { fputc('(', out); erase(t->b, depth); fputc(')', out); }
        break;
    case T_PAPP: erase(t->a, depth); fputc('(', out); erase(t->b, depth); fputc(')', out); break;
    case T_LET:
        if (t->irr) { erase(t->c, depth + 1); break; }
        fprintf(out, "((v%d -> ", depth); erase(t->c, depth + 1); fputs(")(", out); erase(t->b, depth); fputs("))", out); break;
    case T_DEF:
        if (defs[t->n].wordop) fputs(wordop_name(defs[t->n].wordop), out);   /* a word operation is its run-time primitive */
        else if (defs[t->n].isword) fputs("tc_u", out);                     /* the word type: a machine word normalizes to itself */
        else fprintf(out, "tt_%s", defs[t->n].name);
        break;
    case T_NUM: erase(numeral_term(t->n, t->a, t->num), depth); break;   /* a literal is spelled out in constructors, O(log n) */
    case T_IRR: fputs("tc_u", out); break;
    case T_CON: fprintf(out, "tt_c_%s", cons[t->n].name); break;
    case T_ELIM: fprintf(out, "tt_rec_%s", datas[t->n].name); break;
    case T_DATA:   /* inside a code: the block's own codes are the fixpoint variable (a selector of the tuple for a block of several) */
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
    case T_SIGMA: fputs("tc_sigma(", out); erase(t->a, depth); fprintf(out, ")(v%d -> ", depth); erase(t->b, depth + 1); fputc(')', out); break;
    case T_PAIR:
        if (t->n) {   /* at the word type: the machine word */
            if (t->a->k == T_NUM) { char *s = bn_to_dec(t->a->num); fprintf(out, "%sw", s); free(s); }
            else { fputs("tt_nattoword(", out); erase(t->a, depth); fputc(')', out); }
            break;
        }
        fputs("tt_pair(", out); erase(t->a, depth); fputs(")(", out);
        if (t->irr) fputs("tc_u", out); else erase(t->b, depth);   /* an irrelevant component has no run-time content */
        fputc(')', out); break;
    case T_FST:
        if (t->n) { fputs("tt_wtonat(", out); erase(t->a, depth); fputc(')', out); break; }
        fputs("tt_fst(", out); erase(t->a, depth); fputc(')', out); break;
    case T_SND:
        if (t->n) { fputs("tc_u", out); break; }
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

/* only what main reaches is emitted: definitions through their bodies, data types through constructors, eliminators and codes */
static int *def_used, *data_used;
static int uses_words;   /* the program has words: the conversions between Scott naturals and machine words are emitted */
static void mark(Term *t);
/* a data type is used with its whole block: the members' eliminators and codes refer to each other */
static void mark_data(int d) {
    Data *B = &datas[datas[d].block];
    for (int i = 0; i < datas[d].nblock; i++) {
        Data *M = &B[i]; int id = M - datas;
        if (data_used[id]) continue;
        data_used[id] = 1; mark(M->ty);
        for (int ci = 0; ci < M->ncons; ci++) mark(cons[M->cons[ci]].ty);
    }
}
static void mark(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF:
        if (defs[t->n].wordop) { uses_words = 1; break; }   /* the primitive stands for it: its body is not emitted */
        if (defs[t->n].isword) break;
        if (!def_used[t->n]) { def_used[t->n] = 1; mark(defs[t->n].val); }
        break;
    case T_NUM: mark(numeral_term(t->n, t->a, t->num)); break;
    case T_PAIR: if (t->n) uses_words = 1; mark(t->a); if (!t->irr) mark(t->b); break;
    case T_FST: case T_SND: if (t->n) uses_words = 1; mark(t->a); break;
    case T_CON: mark_data(cons[t->n].data); break;
    case T_ELIM: case T_DATA: mark_data(t->n); break;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { mark(t->br[i].face); mark(t->br[i].body); } break;
    case T_APP: mark(t->a); if (!t->irr) mark(t->b); break;
    case T_TRANSP: if (keep_kan || !(t->n || t->b->k == T_I1)) { mark(t->a); mark(t->b); } mark(t->c); break;
    case T_HCOMP: mark(t->a); mark(t->b); mark(t->c); mark(t->d);
        if (t->n) for (int i = 0; i < ndefs; i++) if ((!strcmp(defs[i].name, "transpEquiv") || !strcmp(defs[i].name, "equivProof")) && !def_used[i]) { def_used[i] = 1; mark(defs[i].val); }
        break;
    case T_GLUE: mark(t->a); mark(t->b); mark(t->c);
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "equivProof") && !def_used[i]) { def_used[i] = 1; mark(defs[i].val); }
        break;
    default: mark(t->a); mark(t->b); mark(t->c); mark(t->d); break;
    }
}

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

void erase_program(FILE *f) {
    char *buf = NULL; size_t sz = 0;
    out = open_memstream(&buf, &sz);
    int mainid = -1;
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "main")) mainid = i;
    if (mainid < 0) die("no 'main' definition to run");
    if (defs[mainid].irr) die("'main' is a type; a program must be a value");
    if (nf_main) defs[mainid].val = quote(0, defs[mainid].vval);   /* the checker's normal form instead of the source (rigid: definitions are opaque values) */
    def_used = xalloc((ndefs + 1) * sizeof(int)); data_used = xalloc((ndatas + 1) * sizeof(int));
    def_used[mainid] = 1; mark(defs[mainid].val); mark(defs[mainid].ty);
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
    if (uses_words) {   /* M16a: between the Scott naturals and the machine words */
        fputs("tt_nattoword := fix(self -> n -> n(0w)(k -> wadd(self(k))(1w)))\n", out);
        fputs("tt_wtonat := fix(self -> w -> weq(w)(0w)(h0 -> h1 -> h0)(h0 -> h1 -> h1(self(wsub(w)(1w)))))\n", out);
    }
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
    /* declaration order: data types and definitions interleaved by line number */
    int di = 0, fi = 0;
    while (di < ndatas || fi < ndefs) {
        int take_data = fi >= ndefs || (di < ndatas && datas[di].seq < defs[fi].seq);
        if (take_data) {
            Data *D = &datas[di];
            if (D->nblock > 1) {   /* a mutual block, emitted as a whole at its first member */
                Data *B = &datas[D->block]; int nb = B->nblock; di = D->block + nb;
                if (!data_used[B - datas]) continue;
                for (int i = 0; i < nb; i++) { for (int ci = 0; ci < B[i].ncons; ci++) emit_con(&B[i], ci); if (formal_hcomp(&B[i])) emit_hcomp_con(&B[i]); }
                emit_block_codes(B);
                emit_block_recs(B);
                continue;
            }
            di++;
            if (!data_used[D - datas]) continue;
            for (int ci = 0; ci < D->ncons; ci++) emit_con(D, ci);
            if (formal_hcomp(D)) emit_hcomp_con(D);
            emit_codes(D);
            emit_rec(D);
        } else {
            Def *d = &defs[fi++];
            if (!def_used[d - defs]) continue;
            cur_decl_name = d->name;   /* erasure unfolds redexes, and an inductive lemma at a literal walks it */
            fprintf(out, "tt_%s := ", d->name); erase(d->val, 0); fputc('\n', out);
            if (!strcmp(d->name, "equivProof")) emit_glue_runtime();
            if (!strcmp(d->name, "transpEquiv"))   /* hcomp in the universe: the Glue type of the lid glued along transport back down the sides */
                fputs("tt_hcompU := phi -> u -> u0 -> tc_glue(u0)(phi)(tt_sel(phi)(tt_pair(u(tt_i1))(tt_transpEquiv(i -> u(tt_ineg(i)))))(tt_absurd))\n", out);
        }
    }
    fclose(out);
    /* eezoc reads `defs ; expr`: the separator must follow the last definition on its line */
    if (sz && buf[sz - 1] == '\n') buf[sz - 1] = 0;
    fprintf(f, "%s;\ntt_nf(", buf); out = f; erase(defs[mainid].ty, 0); fprintf(f, ")(tt_%s)\n", defs[mainid].name);
    free(buf);
}
