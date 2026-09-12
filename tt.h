/*
 * tt.h - eezott: a typed front end for eezo.
 *
 * M1: Martin-Lof type theory with a predicative universe hierarchy U 0 < U 1
 * < ..., dependent functions, let, and inductive families with their
 * induction principles (elim D).
 * M2: the cubical layer of CCHM / Cubical Agda: a De Morgan interval I with
 * endpoints, connections and reversal; dependent path types PathP with
 * abstraction and application; partial elements (systems) over faces
 * phi : I; and the Kan operations transp and hcomp, computing on functions,
 * paths, universes and inductive types.
 * M4c: a boundary may apply an earlier path constructor; the eliminator images
 * it as that constructor's method path-applied (or its cube method, taken out
 * of the subtype), and every higher inductive type's induction principle is
 * formed at its declaration.
 * M6: numerals. A decimal literal has no type of its own: it is checked
 * against a data type shaped like the naturals (a nullary constructor and one
 * with a single recursive argument) and elaborates to a term of size
 * O(log n) that doubles the successor along its bits; closed values of such a
 * type print as decimals.
 * M5a: two sorts. U l is the universe of types with Kan structure; Pre l is
 * the sort of pretypes: Partial phi A, Sub A phi u and every function type
 * from I or from/into a pretype. Pretypes may be the types of binders,
 * lets and definitions, never elements of U: no line, path, Glue, Sigma,
 * data argument, motive or Kan operation is formed over one.
 *
 * Programs are checked bidirectionally, definitional equality is decided by
 * normalization by evaluation, and well-typed programs are erased to eezoc
 * source: types vanish, data becomes Scott-encoded, induction becomes a
 * recursive case-analysis, the interval becomes booleans.
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

typedef enum { S_VAR, S_U, S_NUM, S_PI, S_LAM, S_APP, S_LET, S_ELIM,
               S_I, S_I0, S_I1, S_IAND, S_IOR, S_INEG,
               S_PATHP, S_PARTIAL, S_SYS, S_TRANSP, S_HCOMP, S_COMP, S_SUB, S_INS, S_OUTS,
               S_SIGMA, S_PAIR, S_FST, S_SND, S_GLUE, S_GLUEEL, S_UNGLUE } SKind;
typedef struct STerm STerm;
typedef struct { const char *name; STerm *ty; int line; } SBinder;   /* ty NULL for lambda binders */
typedef struct { STerm *face, *body; } SBranch;
struct STerm {
    SKind k; int line;
    const char *name;                 /* S_VAR name; S_ELIM data name; S_LET bound name */
    int lvl;                          /* S_U */
    unsigned long long num;           /* S_NUM: a numeral, checked against a type shaped like the naturals */
    SBinder *binders; int nbinders;   /* S_PI, S_LAM (one binder each after desugaring) */
    STerm *a, *b, *c, *d;             /* S_PI: a=body; S_LAM: a=body; S_APP: a=fn b=arg; S_LET: a=type b=value c=body;
                                         S_IAND/S_IOR: a b; S_INEG: a; S_PATHP: a=line b=x c=y; S_PARTIAL: a=phi b=A;
                                         S_TRANSP: a=line b=phi c=u0; S_HCOMP: a=A b=phi c=u d=u0; S_PAIR: a b */
    SBranch *br; int nbr;             /* S_SYS */
};
typedef struct { const char *name; STerm *ty; STerm *boundary; int line; } SCon;   /* boundary: a system, for path constructors */
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

typedef enum { T_VAR, T_U, T_PI, T_LAM, T_APP, T_LET, T_DEF, T_DATA, T_CON, T_ELIM,
               T_INTERVAL, T_I0, T_I1, T_IAND, T_IOR, T_INEG,
               T_PATHP, T_PAPP, T_PARTIAL, T_SYS, T_TRANSP, T_HCOMP, T_SUB, T_INS, T_OUTS,
               T_SIGMA, T_PAIR, T_FST, T_SND, T_GLUE, T_GLUEEL, T_UNGLUE } TKind;
typedef struct Term Term;
typedef struct { Term *face, *body; } TBranch;
struct Term {
    TKind k;
    int irr;            /* T_PI/T_LAM: binder computationally irrelevant; T_APP: argument irrelevant; T_LET: bound value irrelevant */
    int isi;            /* T_PI/T_LAM: the binder is an interval variable */
    int pre;            /* T_U: the sort Pre l of pretypes; T_PI: the domain is a pretype */
    const char *name;   /* binder name (T_PI/T_LAM/T_LET) */
    int n;              /* T_VAR index; T_U level; T_DEF/T_DATA/T_CON/T_ELIM global id */
    int lv;             /* T_DEF/T_DATA/T_CON/T_ELIM: universe shift of the global (every U n lifted to U n+lv) */
    Term *a, *b, *c, *d;/* T_PI: a=dom b=cod; T_LAM: a=body; T_APP: a=fn b=arg; T_LET: a=type b=val c=body;
                           T_IAND/T_IOR: a b; T_INEG: a; T_PATHP: a=line b=x c=y; T_PAPP: a=path b=r c=x d=y;
                           T_PARTIAL: a=phi b=A; T_TRANSP: a=line b=phi c=u0; T_HCOMP: a=A b=phi c=u d=u0;
                           T_SUB: a=A b=phi c=u; T_INS: a=x; T_OUTS: a=A b=phi c=u d=s;
                           T_SIGMA: a=dom b=cod (under the binder); T_PAIR: a b; T_FST/T_SND: a;
                           T_GLUE: a=A b=phi c=Te; T_GLUEEL: a=ts b=a c=the Glue type; T_UNGLUE: a=b b=A c=phi d=Te */
    TBranch *br; int nbr; /* T_SYS */
};
Term *mk_var(int i); Term *mk_u(int l); Term *mk_upre(int l); Term *mk_pi(const char *x, Term *a, Term *b, int irr);
Term *mk_lam(const char *x, Term *body, int irr); Term *mk_app(Term *f, Term *a, int irr);
Term *mk_let(const char *x, Term *ty, Term *v, Term *body, int irr); Term *mk_ref(TKind k, int id); Term *mk_ref_lv(TKind k, int id, int lv);
Term *shift_univ(Term *t, int k);                   /* lift every universe level by k (globals: shift += k) */
Term *subst_term(Term *t, int idx, Term *v);         /* substitute a closed term for a variable */
Term *mk_term(TKind k, Term *a, Term *b, Term *c, Term *d);
Term *shift(Term *t, int cut, int by);              /* free vars >= cut get +by */
Term *shift2(Term *t, int cut1, int by1, int cut2, int by2); /* vars in [cut1,cut2) get +by1, vars >= cut2 get +by2 */
int term_eq(Term *a, Term *b);
void term_print(FILE *f, Term *t, const char **names, int depth);
int term_mentions_var(Term *t, int idx);

/* ---------------- interval values ---------------- */

/* An element of the free De Morgan algebra on the context's interval
 * variables, in irredundant disjunctive normal form: an OR of ANDs of
 * literals, a literal being a variable (by de Bruijn level) or its
 * reversal.  0 = the empty OR, 1 = an OR containing the empty AND. */
typedef struct { int var, neg; } ILit;
typedef struct { ILit *l; int n; } IConj;
typedef struct { IConj *c; int n; } IVal;
IVal iv_zero(void); IVal iv_one(void); IVal iv_var(int level);
IVal iv_and(IVal a, IVal b); IVal iv_or(IVal a, IVal b); IVal iv_neg(IVal a);
int iv_is_one(IVal a); int iv_is_zero(IVal a); int iv_eq(IVal a, IVal b);
/* a face: a partial assignment of interval variables to endpoints */
typedef struct { int *var; int *val; int n; } Face;
IVal iv_restrict(IVal a, const Face *f);
IVal iv_subst(IVal a, int var, IVal s);      /* substitute s for the variable */
IVal iv_forall(IVal a, int var);             /* the largest face below a not mentioning var */
int iv_faces(IVal phi, Face **out);           /* the faces on which phi = 1 (one per consistent conjunct) */
Face face_join(const Face *a, const Face *b);  /* returns n = -1 if inconsistent */
int iv_mentions(IVal a, int level);

/* ---------------- values ---------------- */

typedef enum { V_LAM, V_PI, V_U, V_NEU, V_DATA, V_CON, V_INTERVAL, V_I, V_PATHP, V_PARTIAL, V_SYS, V_SUB, V_INS, V_SIGMA, V_PAIR, V_GLUE, V_GLUEEL } VKind;
typedef struct Val Val;
typedef struct Env { Val *v; struct Env *next; } Env;
typedef struct { Val *v; int irr; int papp; int proj; Val *x, *y; } Arg;   /* spine entry; papp: path application with endpoints x y; proj: 1 fst, 2 snd */
typedef struct { Arg *a; int n, cap; } VList;
typedef struct Clo Clo;
struct Clo { Env *env; Term *t; Val *(*fn)(void *data, Val *arg); void *data; };   /* fn != NULL => native closure */
typedef enum { H_VAR, H_ELIM, H_TRANSP, H_HCOMP, H_OUTS, H_UNGLUE } HKind;
typedef struct { Val *phi; Val *v; } VBranch;
struct Val {
    VKind k; int irr; const char *name; int isi;
    int pre;            /* V_U: the sort Pre l of pretypes */
    int n;              /* V_U level; V_NEU/H_VAR de Bruijn level; V_NEU/H_ELIM data id; V_DATA data id; V_CON con id */
    int lv;             /* V_DATA/V_CON/H_ELIM: universe shift; V_GLUE: the universe level */
    HKind h;
    Clo clo;            /* V_LAM body; V_PI / V_SIGMA codomain */
    Val *dom;           /* V_PI / V_SIGMA domain */
    VList args;         /* V_NEU spine; V_DATA/V_CON arguments (params first) */
    IVal iv;            /* V_I */
    Val *a, *b, *c;     /* V_PATHP: a=line b=x c=y; V_PARTIAL: a=phi b=A; V_NEU/H_TRANSP: a=line b=phi c=u0 (then spine); V_NEU/H_HCOMP: a=A b=phi c=u, dom=u0;
                           V_SUB: a=A b=phi c=u; V_INS: a=x; V_NEU/H_OUTS: a=A b=phi c=u dom=s; V_PAIR: a b;
                           V_GLUE: a=A b=phi c=Te; V_GLUEEL: a=ts b=a c=the Glue type; V_NEU/H_UNGLUE: a=A b=phi c=Te dom=b */
    VBranch *br; int nbr; /* V_SYS */
};

void vl_push(VList *l, Val *v, int irr);
void vl_push_arg(VList *l, Arg a);
VList vl_copy(const VList *l);
Env *env_push(Env *e, Val *v);
Val *env_get(Env *e, int idx);
Val *vvar(int level); Val *vu(int l); Val *vupre(int l); Val *vi(IVal iv); Val *vivar(int level);
Val *mkval(VKind k);
Val *eval(Env *env, Term *t);
Val *vapp(Val *f, Val *a, int irr);
Val *vpapp(Val *p, Val *r, Val *x, Val *y);
Val *vproj(Val *p, int which);
Val *vlam_native(const char *name, Val *(*fn)(void *, Val *), void *data);
Term *quote(int depth, Val *v);
int conv(int depth, Val *a, Val *b);
Val *inst(Clo *c, Val *v);          /* instantiate a closure */
Val *restrict_val(Val *v, const Face *f);
Val *subst_val(Val *v, int level, IVal s);   /* substitute an interval value for an interval variable */
Val *vglue(Val *A, Val *phi, Val *Te); Val *vglueel(Val *ts, Val *a, Val *G); Val *vunglue(Val *A, Val *phi, Val *Te, Val *b);
Val *vtransp(Val *line, Val *phi, Val *u0);
Val *vhcomp(Val *A, Val *phi, Val *u, Val *u0);
Val *vsys_at(Val *sys, const Face *f);   /* the branch of a system that is total on f (NULL if none) */
Val *vouts(Val *A, Val *phi, Val *u, Val *s);
int val_mentions_ivar(int depth, Val *v, int level);

/* ---------------- globals ---------------- */

typedef struct { const char *name; Term *ty; Term *val; Val *vty; Val *vval; int irr; int line; Val **vty_lv, **vval_lv; int nlv; int poly; } Def;
/* poly: the global mentions a universe (directly or through another polymorphic global); only then does a universe shift change it */
typedef struct {
    const char *name; Term *ty; int irr;   /* type of the argument, under [params, previous args] */
    int isrec, npi;                        /* recursive: type is (y_1..y_npi) -> D params idx */
    Term **idx; int nidx;                  /* index terms of the recursive occurrence, under [params, prev args, y's] */
    int isrecpath; Term *px, *py;          /* recursive path argument: type is Path (D params) px py (endpoints under [params, prev args]) */
} ConArg;
typedef struct {
    const char *name; int data, ci; Term *ty; int line;
    ConArg *args; int nargs; int nrec;
    Term **ridx;                           /* return index terms, under [params, args] */
    int nint;                              /* path constructor: number of interval binders after the arguments */
    Term *boundary;                        /* its boundary: a system under [params, args, intervals] (NULL: none) */
    int bparams;                           /* the boundary mentions the parameters (they are then kept at run time) */
    int pathmethod;                        /* the eliminator's method is a PathP (one interval, boundary at both ends) */
} Con;
typedef struct {
    const char *name; int line;
    int nparams, nidx, lvl;
    Term **ptys;                           /* param types, each under the previous params */
    Term **itys;                           /* index types, each under [params, previous indices] */
    Term *ty;                              /* the type of the data constant: params -> indices -> U lvl */
    int *cons; int ncons;
    int poly;
    int hit;                               /* has path constructors: hcomp is a normal form */
} Data;

Val *def_val(int id, int lv); Val *def_ty(int id, int lv);   /* a definition at a universe shift (memoised) */
Term *con_arg_ty(Con *C, int j, int lv);                     /* a constructor argument's type at a shift */
Term *data_ty(int d, int lv); Term *con_ty(int c, int lv);
int term_poly(Term *t);                                      /* does the term mention a universe (or a polymorphic global)? */

extern Def *defs; extern int ndefs;
extern Data *datas; extern int ndatas;
extern Con *cons; extern int ncons;

int is_type_like(int depth, Val *ty);      /* U or a family into U: computationally irrelevant */
int peano_shape(int d, int *zero, int *suc);  /* a data type shaped like the naturals, with its zero and successor */
void elab_program(SDecl *decls);
void erase_program(FILE *out);
extern int keep_kan;                 /* erase every transport, even along constant lines */

#endif
