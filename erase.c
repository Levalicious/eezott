/*
 * erase.c - erasure of checked programs to eezoc source.
 *
 * Types, universes, motives, indices and every binder or argument marked
 * irrelevant vanish.  Constructors become Scott selectors; the induction
 * principle of a data type becomes a recursive case analysis built with
 * the prelude's fix.  The interval becomes the Scott booleans (i0 false,
 * i1 true; meet, join and reversal the boolean operations), paths become
 * functions of a boolean, systems a chain of boolean choices, and hcomp
 * the choice between its sides at i1 and its base.  transp is dropped
 * along lines the elaborator proved constant; along any other line it has
 * no run-time meaning without type codes, and erasure refuses it.
 * Output is ordinary eezoc source: definitions in dependency order, then
 * `;` and the program's main term.
 */
#include "tt.h"

static FILE *out;

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
    case T_DEF:
        if (defs[t->n].irr) die("internal: erased definition '%s' used at run time", defs[t->n].name);
        fprintf(out, "tt_%s", defs[t->n].name); break;
    case T_CON: fprintf(out, "tt_c_%s", cons[t->n].name); break;
    case T_ELIM: fprintf(out, "tt_rec_%s", datas[t->n].name); break;
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
        fputs("tt_hcomp(", out); erase(t->b, depth); fputs(")(", out); erase(t->c, depth); fputs(")(", out); erase(t->d, depth); fputc(')', out); break;
    case T_TRANSP:
        if (t->n || t->b->k == T_I1) { erase(t->c, depth); break; }
        die("transp along a line that is not constant reaches run time; this needs run-time type codes and is not erasable yet");
    case T_INS: erase(t->a, depth); break;
    case T_OUTS: erase(t->d, depth); break;
    case T_U: case T_PI: case T_DATA: case T_INTERVAL: case T_PATHP: case T_PARTIAL: case T_SUB:
        die("internal: a type reached erasure in a relevant position");
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


/* only what main reaches is emitted: definitions through their bodies, data types through constructors and eliminators */
static int *def_used, *data_used;
static void mark(Term *t) {
    if (!t) return;
    switch (t->k) {
    case T_DEF: if (!def_used[t->n]) { def_used[t->n] = 1; if (!defs[t->n].irr) mark(defs[t->n].val); } break;
    case T_CON: data_used[cons[t->n].data] = 1; break;
    case T_ELIM: data_used[t->n] = 1; break;
    case T_SYS: for (int i = 0; i < t->nbr; i++) { mark(t->br[i].face); mark(t->br[i].body); } break;
    case T_APP: mark(t->a); if (!t->irr) mark(t->b); break;
    case T_LAM: if (!t->irr) mark(t->a); else mark(t->a); break;
    case T_LET: mark(t->b); mark(t->c); break;
    case T_TRANSP: mark(t->c); break;
    case T_HCOMP: mark(t->b); mark(t->c); mark(t->d); break;
    case T_PAPP: mark(t->a); mark(t->b); break;
    case T_INS: mark(t->a); break;
    case T_OUTS: mark(t->d); break;
    case T_IAND: case T_IOR: case T_INEG: mark(t->a); mark(t->b); break;
    default: break;
    }
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
    /* the interval as Scott booleans; the run-time meaning of systems and hcomp */
    fputs("tt_i0 := t -> f -> f\n", out);
    fputs("tt_i1 := t -> f -> t\n", out);
    fputs("tt_iand := a -> b -> a(b)(tt_i0)\n", out);
    fputs("tt_ior := a -> b -> a(tt_i1)(b)\n", out);
    fputs("tt_ineg := a -> a(tt_i0)(tt_i1)\n", out);
    fputs("tt_absurd := x -> x\n", out);
    fputs("tt_hcomp := phi -> u -> u0 -> phi(u(tt_i1))(u0)\n", out);
    /* declaration order: data types and definitions interleaved by line number */
    int di = 0, fi = 0;
    while (di < ndatas || fi < ndefs) {
        int take_data = fi >= ndefs || (di < ndatas && datas[di].line < defs[fi].line);
        if (take_data) {
            Data *D = &datas[di++];
            if (!data_used[D - datas]) continue;
            for (int ci = 0; ci < D->ncons; ci++) emit_con(D, ci);
            emit_rec(D);
        } else {
            Def *d = &defs[fi++];
            if (d->irr || !def_used[d - defs]) continue;
            fprintf(out, "tt_%s := ", d->name); erase(d->val, 0); fputc('\n', out);
        }
    }
    fclose(out);
    /* eezoc reads `defs ; expr`: the separator must follow the last definition on its line */
    if (sz && buf[sz - 1] == '\n') buf[sz - 1] = 0;
    fprintf(f, "%s;\ntt_%s\n", buf, defs[mainid].name);
    free(buf);
}
