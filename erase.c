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
 * case analysis built with the prelude's fix; the interval becomes the
 * Scott booleans; hcomp is the choice between its sides at i1 and its base.
 * hcomp in the universe has no run-time meaning before Glue and is refused.
 * Output is ordinary eezoc source: definitions in dependency order, then
 * `;` and the program's main term.
 */
#include "tt.h"

int keep_kan;
static FILE *out;
static int self_data = -1;      /* while emitting tt_transp_D: references to D go through the fixpoint's self */

static void erase(Term *t, int depth) {
    switch (t->k) {
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
    case T_DEF: fprintf(out, "tt_%s", defs[t->n].name); break;
    case T_CON: fprintf(out, "tt_c_%s", cons[t->n].name); break;
    case T_ELIM: fprintf(out, "tt_rec_%s", datas[t->n].name); break;
    case T_DATA:
        if (t->n == self_data) fprintf(out, "tcs_%s(self)", datas[t->n].name); else fprintf(out, "tc_%s", datas[t->n].name);
        break;
    case T_U: case T_INTERVAL: case T_PARTIAL: case T_SUB: fputs("tc_u", out); break;
    case T_PI: fputs("tc_pi(", out); erase(t->a, depth); fprintf(out, ")(v%d -> ", depth); erase(t->b, depth + 1); fputc(')', out); break;
    case T_PATHP: fputs("tc_path(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_I0: fputs("tt_i0", out); break;
    case T_I1: fputs("tt_i1", out); break;
    case T_IAND: fputs("tt_iand(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputc(')', out); break;
    case T_IOR: fputs("tt_ior(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputc(')', out); break;
    case T_INEG: fputs("tt_ineg(", out); erase(t->a, depth); fputc(')', out); break;
    case T_SYS:
        for (int i = 0; i < t->nbr; i++) { erase(t->br[i].face, depth); fputc('(', out); erase(t->br[i].body, depth); fputs(")(", out); }
        fputs("tt_absurd", out);
        for (int i = 0; i < t->nbr; i++) fputc(')', out);
        break;
    case T_HCOMP:
        if (t->n) die("hcomp in the universe reaches run time; it has no run-time meaning before Glue (M3)");
        fputs("tt_hcomp(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputc(')', out); break;
    case T_TRANSP:
        if (!keep_kan && (t->n || t->b->k == T_I1)) { erase(t->c, depth); break; }     /* a constant line: the identity */
        fputs("tt_transp(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_INS: erase(t->a, depth); break;
    case T_OUTS: erase(t->d, depth); break;
    case T_SIGMA: fputs("tc_sigma(", out); erase(t->a, depth); fprintf(out, ")(v%d -> ", depth); erase(t->b, depth + 1); fputc(')', out); break;
    case T_PAIR: fputs("tt_pair(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputc(')', out); break;
    case T_FST: fputs("tt_fst(", out); erase(t->a, depth); fputc(')', out); break;
    case T_SND: fputs("tt_snd(", out); erase(t->a, depth); fputc(')', out); break;
    case T_GLUE: fputs("tc_glue(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputc(')', out); break;
    case T_GLUEEL: fputs("tt_glue(", out); erase(t->c->b, depth); fputs(")(", out); erase(t->a, depth); fputs(")(", out); erase(t->b, depth); fputc(')', out); break;
    case T_UNGLUE: fputs("tt_unglue(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputs(")(", out); erase(t->a, depth); fputc(')', out); break;
    }
}

/* Scott constructor: relevant args, then one handler per constructor, select own handler */
static void emit_con(Data *D, int ci) {
    Con *C = &cons[D->cons[ci]];
    fprintf(out, "tt_c_%s := ", C->name);
    for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "a%d -> ", j);
    for (int i = 0; i < D->ncons; i++) fprintf(out, "h%d -> ", i);
    fprintf(out, "h%d", ci);
    for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "(a%d)", j);
    fputc('\n', out);
}

/* tt_rec_D := fix(rec -> m0 -> .. -> x -> x(case_0)..(case_k)) */
static void emit_rec(Data *D) {
    fprintf(out, "tt_rec_%s := fix(rec -> ", D->name);
    for (int i = 0; i < D->ncons; i++) fprintf(out, "m%d -> ", i);
    fputs("x -> x", out);
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fputc('(', out);
        for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "a%d -> ", j);
        fprintf(out, "m%d", ci);
        for (int j = 0; j < C->nargs; j++) if (!C->args[j].irr) fprintf(out, "(a%d)", j);
        for (int j = 0; j < C->nargs; j++) {
            ConArg *A = &C->args[j];
            if (!A->isrec) continue;
            /* induction hypothesis: \y_rel.. -> rec m.. (a_j y_rel..) */
            fputc('(', out);
            Term *w = A->ty; int yt = 0;
            for (Term *p = w; p->k == T_PI && yt < A->npi; p = p->b, yt++) if (!p->irr) fprintf(out, "y%d -> ", yt);
            fputs("rec", out);
            for (int i = 0; i < D->ncons; i++) fprintf(out, "(m%d)", i);
            fprintf(out, "(a%d", j);
            yt = 0;
            for (Term *p = w; p->k == T_PI && yt < A->npi; p = p->b, yt++) if (!p->irr) fprintf(out, "(y%d)", yt);
            fputs("))", out);
        }
        fputc(')', out);
    }
    fputs(")\n", out);
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
        fputs("(line(i)(m -> ", out);
        for (int p = 0; p < np; p++) fprintf(out, "p%d -> ", p);
        fprintf(out, "p%d))", k);
    }
    for (int k = 0; k < j; k++) fprintf(out, "(fl%d(i))", k);
    fputc(')', out);
}

/* tcs_D := tr -> p.. -> k -> k(tr)(p..);  tt_transp_D := fix(self -> p.. -> line -> phi -> x -> x(case..));  tc_D := tcs_D(tt_transp_D) */
static void emit_codes(Data *D) {
    int np = D->nparams;
    fprintf(out, "tcs_%s := tr -> ", D->name);
    for (int p = 0; p < np; p++) fprintf(out, "p%d -> ", p);
    fputs("k -> k(tr)", out);
    for (int p = 0; p < np; p++) fprintf(out, "(p%d)", p);
    fputc('\n', out);
    fprintf(out, "tt_transp_%s := fix(self -> ", D->name);
    for (int p = 0; p < np; p++) fprintf(out, "p%d -> ", p);
    fputs("line -> phi -> x -> x", out);
    self_data = D - datas;
    for (int ci = 0; ci < D->ncons; ci++) {
        Con *C = &cons[D->cons[ci]];
        fputc('(', out);
        for (int j = 0; j < C->nargs; j++) fprintf(out, "a%d -> ", j);
        /* bind the fillers of every argument but the last, in order */
        for (int j = 0; j + 1 < C->nargs; j++) fprintf(out, "(fl%d -> ", j);
        fprintf(out, "tt_c_%s", C->name);
        for (int j = 0; j < C->nargs; j++) {
            fputs("(tt_transp", out); emit_arg_line(D, C, j); fprintf(out, "(phi)(a%d))", j);
        }
        for (int j = C->nargs - 2; j >= 0; j--) {
            /* fl_j := i -> transp (k -> A_j(i /\ k)) (phi \/ ~i) a_j */
            fputs(")(i -> tt_transp(k -> ", out); emit_arg_line(D, C, j); fprintf(out, "(tt_iand(i)(k)))(tt_ior(phi)(tt_ineg(i)))(a%d))", j);
        }
        fputc(')', out);
    }
    self_data = -1;
    fputs(")\n", out);
    fprintf(out, "tc_%s := tcs_%s(tt_transp_%s)\n", D->name, D->name, D->name);
}

/* only what main reaches is emitted: definitions through their bodies, data types through constructors, eliminators and codes */
static int *def_used, *data_used;
static void mark(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF: if (!def_used[t->n]) { def_used[t->n] = 1; mark(defs[t->n].val); } break;
    case T_CON: if (!data_used[cons[t->n].data]) { data_used[cons[t->n].data] = 1; mark(datas[cons[t->n].data].ty); for (int ci = 0; ci < datas[cons[t->n].data].ncons; ci++) mark(cons[datas[cons[t->n].data].cons[ci]].ty); } break;
    case T_ELIM: case T_DATA: if (!data_used[t->n]) { data_used[t->n] = 1; mark(datas[t->n].ty); for (int ci = 0; ci < datas[t->n].ncons; ci++) mark(cons[datas[t->n].cons[ci]].ty); } break;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { mark(t->br[i].face); mark(t->br[i].body); } break;
    case T_APP: mark(t->a); if (!t->irr) mark(t->b); break;
    case T_TRANSP: if (keep_kan || !(t->n || t->b->k == T_I1)) { mark(t->a); mark(t->b); } mark(t->c); break;
    case T_HCOMP: mark(t->b); mark(t->c); mark(t->d); break;
    case T_GLUE: mark(t->a); mark(t->b); mark(t->c);
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "equivProof") && !def_used[i]) { def_used[i] = 1; mark(defs[i].val); }
        break;
    default: mark(t->a); mark(t->b); mark(t->c); mark(t->d); break;
    }
}

/* the run-time Glue layer: emitted right after the prelude's equivProof, which its transport rule calls */
static void emit_glue_runtime(void) {
    /* Glue: an element is the glued element itself where phi holds, and otherwise the pair (sides, base) */
    fputs("tt_glue := phi -> ts -> a -> phi(ts)(tt_pair(ts)(a))\n", out);
    fputs("tt_unglue := phi -> te -> b -> phi(tt_fst(tt_snd(te))(b))(tt_snd(b))\n", out);
    fputs("tt_gA := c -> c(m -> a -> phi -> te -> a)\n", out);
    fputs("tt_gphi := c -> c(m -> a -> phi -> te -> phi)\n", out);
    fputs("tt_gte := c -> c(m -> a -> phi -> te -> te)\n", out);
    fputs("tt_gcomp := line -> phi -> u -> u0 -> tt_hcomp(tt_ior(phi)(tt_ineg(phi)))(i -> phi(tt_transp(j -> line(tt_ior(i)(j)))(i)(u(i)))(tt_transp(line)(tt_i0)(u0)))(tt_transp(line)(tt_i0)(u0))\n", out);
    /* transport along a line of Glue types, as in the checker: at run time every interval value is an endpoint */
    fputs("tt_transp_glue := a -> phi -> te -> line -> psi -> u0 -> "
          "(fa -> (ungl -> (tf -> (a1 -> (phi1 -> (te1 -> "
          "(fib -> tt_glue(phi1)(tt_fst(fib))(tt_hcomp(tt_ior(phi1)(psi))(j -> phi1(tt_snd(fib)(tt_ineg(j)))(a1))(a1)))"
          "(tt_equivProof(tt_fst(te1))(tt_gA(line(tt_i1)))(tt_snd(te1))(a1)(tt_ior(psi)(fa))"
          "(psi(tt_pair(u0)(j -> a1))(fa(tt_pair(tf(tt_i1))(j -> a1))(tt_absurd)))))"
          "(tt_gte(line(tt_i1))))(tt_gphi(line(tt_i1))))"
          "(tt_gcomp(i -> tt_gA(line(i)))(tt_ior(psi)(fa))(i -> psi(ungl(i))(fa(tt_fst(tt_snd(tt_gte(line(i))))(tf(i)))(tt_absurd)))(ungl(tt_i0))))"
          "(i -> tt_transp(j -> tt_fst(tt_gte(line(tt_iand(i)(j)))))(tt_ior(psi)(tt_ineg(i)))(u0)))"
          "(i -> tt_unglue(tt_gphi(line(i)))(tt_gte(line(i)))(u0)))"
          "(tt_iand(tt_gphi(line(tt_i0)))(tt_gphi(line(tt_i1))))\n", out);
    fputs("tc_glue := a -> phi -> te -> k -> k(tt_transp_glue)(a)(phi)(te)\n", out);
}

void erase_program(FILE *f) {
    char *buf = NULL; size_t sz = 0;
    out = open_memstream(&buf, &sz);
    int mainid = -1;
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "main")) mainid = i;
    if (mainid < 0) die("no 'main' definition to run");
    if (defs[mainid].irr) die("'main' is a type; a program must be a value");
    def_used = xalloc((ndefs + 1) * sizeof(int)); data_used = xalloc((ndatas + 1) * sizeof(int));
    def_used[mainid] = 1; mark(defs[mainid].val);
    fputs("#import prelude\n", out);
    /* the interval as Scott booleans; the run-time meaning of systems, hcomp, transport and the codes of the basic type formers */
    fputs("tt_i0 := t -> f -> f\n", out);
    fputs("tt_i1 := t -> f -> t\n", out);
    fputs("tt_iand := a -> b -> a(b)(tt_i0)\n", out);
    fputs("tt_ior := a -> b -> a(tt_i1)(b)\n", out);
    fputs("tt_ineg := a -> a(tt_i0)(tt_i1)\n", out);
    fputs("tt_absurd := x -> x\n", out);
    fputs("tt_hcomp := phi -> u -> u0 -> phi(u(tt_i1))(u0)\n", out);
    fputs("tt_transp := line -> phi -> a -> phi(a)(line(tt_i0)(m -> m)(line)(phi)(a))\n", out);
    fputs("tt_comp := line -> phi -> u -> u0 -> tt_hcomp(phi)(i -> tt_transp(j -> line(tt_ior(i)(j)))(i)(u(i)))(tt_transp(line)(tt_i0)(u0))\n", out);
    fputs("tt_transp_u := line -> phi -> a -> a\n", out);
    fputs("tc_u := k -> k(tt_transp_u)\n", out);
    fputs("tt_dom := c -> c(m -> d -> b -> d)\n", out);
    fputs("tt_cod := c -> c(m -> d -> b -> b)\n", out);
    fputs("tt_transp_pi := d -> b -> line -> phi -> f -> x -> (v -> tt_transp(i -> tt_cod(line(i))(v(i)))(phi)(f(v(tt_i0))))"
          "(i -> tt_transp(j -> tt_dom(line(tt_ior(i)(tt_ineg(j)))))(tt_ior(phi)(i))(x))\n", out);
    fputs("tc_pi := d -> b -> k -> k(tt_transp_pi)(d)(b)\n", out);
    fputs("tt_pline := c -> c(m -> l -> x -> y -> l)\n", out);
    fputs("tt_px := c -> c(m -> l -> x -> y -> x)\n", out);
    fputs("tt_py := c -> c(m -> l -> x -> y -> y)\n", out);
    fputs("tt_transp_path := l -> x -> y -> line -> phi -> p -> j -> tt_comp(i -> tt_pline(line(i))(j))(tt_ior(phi)(tt_ior(j)(tt_ineg(j))))"
          "(i -> phi(p(j))(tt_ineg(j)(tt_px(line(i)))(j(tt_py(line(i)))(tt_absurd))))(p(j))\n", out);
    fputs("tc_path := l -> x -> y -> k -> k(tt_transp_path)(l)(x)(y)\n", out);
    fputs("tt_pair := a -> b -> k -> k(a)(b)\n", out);
    fputs("tt_fst := p -> p(a -> b -> a)\n", out);
    fputs("tt_snd := p -> p(a -> b -> b)\n", out);
    fputs("tt_transp_sigma := d -> b -> line -> phi -> p -> tt_pair(tt_transp(i -> tt_dom(line(i)))(phi)(tt_fst(p)))"
          "(tt_transp(i -> tt_cod(line(i))(tt_transp(j -> tt_dom(line(tt_iand(i)(j))))(tt_ior(phi)(tt_ineg(i)))(tt_fst(p))))(phi)(tt_snd(p)))\n", out);
    fputs("tc_sigma := d -> b -> k -> k(tt_transp_sigma)(d)(b)\n", out);
    /* declaration order: data types and definitions interleaved by line number */
    int di = 0, fi = 0;
    while (di < ndatas || fi < ndefs) {
        int take_data = fi >= ndefs || (di < ndatas && datas[di].line < defs[fi].line);
        if (take_data) {
            Data *D = &datas[di++];
            if (!data_used[D - datas]) continue;
            for (int ci = 0; ci < D->ncons; ci++) emit_con(D, ci);
            emit_rec(D);
            emit_codes(D);
        } else {
            Def *d = &defs[fi++];
            if (!def_used[d - defs]) continue;
            fprintf(out, "tt_%s := ", d->name); erase(d->val, 0); fputc('\n', out);
            if (!strcmp(d->name, "equivProof")) emit_glue_runtime();
        }
    }
    fclose(out);
    /* eezoc reads `defs ; expr`: the separator must follow the last definition on its line */
    if (sz && buf[sz - 1] == '\n') buf[sz - 1] = 0;
    fprintf(f, "%s;\ntt_%s\n", buf, defs[mainid].name);
    free(buf);
}
