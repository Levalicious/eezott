/*
 * erase.c - erasure of checked programs to eezoc source.
 *
 * Types, universes, motives, indices and every binder or argument marked
 * irrelevant vanish.  Constructors become Scott selectors; the induction
 * principle of a data type becomes a recursive case analysis built with
 * the prelude's fix.  Output is ordinary eezoc source: definitions in
 * dependency order, then `;` and the program's main term.
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
    case T_LET:
        if (t->irr) { erase(t->c, depth + 1); break; }
        fprintf(out, "((v%d -> ", depth); erase(t->c, depth + 1); fputs(")(", out); erase(t->b, depth); fputs("))", out); break;
    case T_DEF:
        if (defs[t->n].irr) die("internal: erased definition '%s' used at run time", defs[t->n].name);
        fprintf(out, "tt_%s", defs[t->n].name); break;
    case T_CON: fprintf(out, "tt_c_%s", cons[t->n].name); break;
    case T_ELIM: fprintf(out, "tt_rec_%s", datas[t->n].name); break;
    case T_U: case T_PI: case T_DATA: die("internal: a type reached erasure in a relevant position");
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

void erase_program(FILE *f) {
    char *buf = NULL; size_t sz = 0;
    out = open_memstream(&buf, &sz);
    int mainid = -1;
    for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, "main")) mainid = i;
    if (mainid < 0) die("no 'main' definition to run");
    if (defs[mainid].irr) die("'main' is a type; a program must be a value");
    fputs("#import prelude\n", out);
    /* declaration order: data types and definitions interleaved by line number */
    int di = 0, fi = 0;
    while (di < ndatas || fi < ndefs) {
        int take_data = fi >= ndefs || (di < ndatas && datas[di].line < defs[fi].line);
        if (take_data) {
            Data *D = &datas[di++];
            for (int ci = 0; ci < D->ncons; ci++) emit_con(D, ci);
            emit_rec(D);
        } else {
            Def *d = &defs[fi++];
            if (d->irr) continue;
            fprintf(out, "tt_%s := ", d->name); erase(d->val, 0); fputc('\n', out);
        }
    }
    fclose(out);
    /* eezoc reads `defs ; expr`: the separator must follow the last definition on its line */
    if (sz && buf[sz - 1] == '\n') buf[sz - 1] = 0;
    fprintf(f, "%s;\ntt_%s\n", buf, defs[mainid].name);
    free(buf);
}
