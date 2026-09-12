/*
 * tt.h - eezott: a typed front end for eezo.
 *
 * M1: Martin-Lof type theory with a predicative universe hierarchy U 0 < U 1
 * < ..., dependent functions, let, and inductive families with their
 * induction principles (elim D).  Programs are checked bidirectionally,
 * definitional equality is decided by normalization by evaluation, and
 * well-typed programs are erased to eezoc source: types vanish, data becomes
 * Scott-encoded, induction becomes a recursive case-analysis.
 */
#ifndef EEZOTT_H
#define EEZOTT_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "../libeezo/types.h"

void *xalloc(size_t n);
char *xstrdup(const char *s);
char *xsprintf(const char *fmt, ...);
void die(const char *fmt, ...);

/* ---------------- surface syntax ---------------- */

typedef enum { S_VAR, S_U, S_PI, S_LAM, S_APP, S_LET, S_ELIM } SKind;
typedef struct STerm STerm;
typedef struct { const char *name; STerm *ty; int line; } SBinder;   /* ty NULL for lambda binders */
struct STerm {
    SKind k; int line;
    const char *name;                 /* S_VAR name; S_ELIM data name; S_LET bound name */
    int lvl;                          /* S_U */
    SBinder *binders; int nbinders;   /* S_PI, S_LAM (one binder each after desugaring) */
    STerm *a, *b, *c;                 /* S_PI: a=body; S_LAM: a=body; S_APP: a=fn b=arg; S_LET: a=type b=value c=body */
};
typedef struct { const char *name; STerm *ty; int line; } SCon;
typedef struct SDecl {
    int isdata; const char *name; int line;
    SBinder *params; int nparams;     /* data: parameters; def: binder sugar folded into ty/val */
    STerm *ty;                        /* def: type; data: index telescope ending in U */
    STerm *val;                       /* def */
    SCon *cons; int ncons;            /* data */
    struct SDecl *next;
} SDecl;

SDecl *parse_program(const char *src, const char *fname);

/* ---------------- core terms (de Bruijn indices) ---------------- */

typedef enum { T_VAR, T_U, T_PI, T_LAM, T_APP, T_LET, T_DEF, T_DATA, T_CON, T_ELIM } TKind;
typedef struct Term Term;
struct Term {
    TKind k;
    int irr;            /* T_PI/T_LAM: binder computationally irrelevant; T_APP: argument irrelevant; T_LET: bound value irrelevant */
    const char *name;   /* binder name (T_PI/T_LAM/T_LET) */
    int n;              /* T_VAR index; T_U level; T_DEF/T_DATA/T_CON/T_ELIM global id */
    Term *a, *b, *c;    /* T_PI: a=dom b=cod; T_LAM: a=body; T_APP: a=fn b=arg; T_LET: a=type b=val c=body */
};
Term *mk_var(int i); Term *mk_u(int l); Term *mk_pi(const char *x, Term *a, Term *b, int irr);
Term *mk_lam(const char *x, Term *body, int irr); Term *mk_app(Term *f, Term *a, int irr);
Term *mk_let(const char *x, Term *ty, Term *v, Term *body, int irr); Term *mk_ref(TKind k, int id);
Term *shift(Term *t, int cut, int by);              /* free vars >= cut get +by */
Term *shift2(Term *t, int cut1, int by1, int cut2, int by2); /* vars in [cut1,cut2) get +by1, vars >= cut2 get +by2 */
int term_eq(Term *a, Term *b);
void term_print(FILE *f, Term *t, const char **names, int depth);

/* ---------------- values ---------------- */

typedef enum { V_LAM, V_PI, V_U, V_NEU, V_DATA, V_CON } VKind;
typedef struct Val Val;
typedef struct Env { Val *v; struct Env *next; } Env;
typedef struct { Val **v; int n, cap; } VList;
typedef struct IhClo IhClo;
typedef struct { Env *env; Term *t; IhClo *ih; } Clo;     /* t==NULL => native induction-hypothesis closure */
typedef enum { H_VAR, H_ELIM } HKind;
struct Val {
    VKind k; int irr; const char *name;
    int n;              /* V_U level; V_NEU/H_VAR de Bruijn level; V_NEU/H_ELIM data id; V_DATA data id; V_CON con id */
    HKind h;
    Clo clo;            /* V_LAM body; V_PI codomain */
    Val *dom;           /* V_PI */
    VList args;         /* V_NEU spine; V_DATA/V_CON arguments (params first) */
};

void vl_push(VList *l, Val *v);
VList vl_copy(const VList *l);
Env *env_push(Env *e, Val *v);
Val *env_get(Env *e, int idx);
Val *vvar(int level); Val *vu(int l);
Val *eval(Env *env, Term *t);
Val *vapp(Val *f, Val *a, int irr);
Term *quote(int depth, Val *v);
int conv(int depth, Val *a, Val *b);
Val *inst(Clo *c, Val *v);          /* instantiate a closure */

/* ---------------- globals ---------------- */

typedef struct { const char *name; Term *ty; Term *val; Val *vty; Val *vval; int irr; int line; } Def;
typedef struct {
    const char *name; Term *ty; int irr;   /* type of the argument, under [params, previous args] */
    int isrec, npi;                        /* recursive: type is (y_1..y_npi) -> D params idx */
    Term **idx; int nidx;                  /* index terms of the recursive occurrence, under [params, prev args, y's] */
} ConArg;
typedef struct {
    const char *name; int data, ci; Term *ty; int line;
    ConArg *args; int nargs; int nrec;
    Term **ridx;                           /* return index terms, under [params, args] */
} Con;
typedef struct {
    const char *name; int line;
    int nparams, nidx, lvl;
    Term **ptys;                           /* param types, each under the previous params */
    Term **itys;                           /* index types, each under [params, previous indices] */
    Term *ty;                              /* the type of the data constant: params -> indices -> U lvl */
    int *cons; int ncons;
} Data;

extern Def *defs; extern int ndefs;
extern Data *datas; extern int ndatas;
extern Con *cons; extern int ncons;

int is_type_like(int depth, Val *ty);      /* U or a family into U: computationally irrelevant */
void elab_program(SDecl *decls);
void erase_program(FILE *out);

#endif
