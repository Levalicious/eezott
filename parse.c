/*
 * parse.c - eezott lexer and recursive-descent parser.
 *
 *   program  := decl*
 *   decl     := 'def' name binder* ':' term ':=' term
 *             | 'data' name binder* ':' term 'where' ('|' name ':' term system?)*   (a system: the boundary of a path constructor)
 *             | 'mutual' binder* ('data' name ':' term 'where' ...)+ 'end'          (a block sharing the binders as parameters)
 *   binder   := '(' name+ ':' term ')' | '{' name+ ':' term '}'      (implicit)
 *   term     := binder+ '->' term            dependent function type
 *             | '\' (name | '{' name '}')+ '->' term    lambda / path abstraction
 *             | 'let' name ':' term ':=' term 'in' term
 *             | ior ('->' term)?             non-dependent arrow
 *   ior      := iand ('\/' iand)*            interval join
 *   iand     := neg ('/\' neg)*              interval meet
 *   neg      := '~' neg | app                interval reversal
 *   app      := atom (atom | '{' term '}')*    ({e} supplies the next implicit argument)
 *   atom     := name | '_' | 'U' [0-9]+? | 'I' | 'i0' | 'i1' | 'elim' name | '(' term ')'      ('_': a hole)
 *             | 'PathP' | 'Path' | 'Partial' | 'transp' | 'hcomp' | 'comp'   (heads, applied like functions)
 *             | 'Sub' | 'inS' | 'outS'                                     (cubical subtypes A [ phi |-> u ])
 *             | 'Sigma' | 'fst' | 'snd' | '(' term ',' term ')'                (dependent pairs)
 *             | 'Glue' | 'glue' | 'unglue'                                  (Glue types: univalence)
 *             | '[' (ior '->' term ('|' ior '->' term)*)? ']'          (system of partial elements)
 *   comments: '#' or '--' to end of line.
 */
#include "tt.h"
#include "machine.h"
#include <ctype.h>
#include <errno.h>

typedef enum { TK_EOF, TK_NAME, TK_NUM, TK_LP, TK_RP, TK_LB, TK_RB, TK_COLON, TK_DEFEQ, TK_ARROW, TK_LAM, TK_BAR,
               TK_TILDE, TK_AND, TK_OR,
               TK_DEF, TK_DATA, TK_WHERE, TK_LET, TK_IN, TK_ELIM, TK_U, TK_I, TK_I0, TK_I1,
               TK_PATHP, TK_PATH, TK_PARTIAL, TK_TRANSP, TK_HCOMP, TK_COMP, TK_SUB, TK_INS, TK_OUTS,
               TK_COMMA, TK_SIGMA, TK_FST, TK_SND, TK_GLUE, TK_GLUEEL, TK_UNGLUE,
               TK_LBRACE, TK_RBRACE, TK_LEVEL, TK_LZERO, TK_LSUC, TK_LMAX, TK_MUTUAL, TK_END, TK_NATIVE, TK_WORD, TK_DOT } TokKind;
typedef struct { TokKind k; const char *s; int n; int line; } Tok;

static Tok *toks; static int ntoks, tcap, pos; static const char *file;
static int in_con_type;   /* while parsing a constructor's type: a following system is its boundary, not an argument */

static void addtok(TokKind k, const char *s, int n, int line) {
    if (ntoks == tcap) { tcap = tcap ? 2 * tcap : 256; toks = rrealloc(toks, tcap * sizeof(Tok)); }
    Tok *t = &toks[ntoks++]; t->k = k; t->s = s; t->n = n; t->line = line;
}
static int isident(int c) { return isalnum(c) || c == '_' || c == '\''; }

static void lex(const char *src) {
    ntoks = 0;   /* each file is lexed on its own (imports, M16b) */
    int line = 1; const char *p = src;
    while (*p) {
        if (*p == '\n') { line++; p++; continue; }
        if (isspace((unsigned char)*p)) { p++; continue; }
        if (*p == '#' || (p[0] == '-' && p[1] == '-')) { while (*p && *p != '\n') p++; continue; }
        if (p[0] == ':' && p[1] == '=') { addtok(TK_DEFEQ, p, 2, line); p += 2; continue; }
        if (p[0] == '-' && p[1] == '>') { addtok(TK_ARROW, p, 2, line); p += 2; continue; }
        if (p[0] == '/' && p[1] == '\\') { addtok(TK_AND, p, 2, line); p += 2; continue; }
        if (p[0] == '\\' && p[1] == '/') { addtok(TK_OR, p, 2, line); p += 2; continue; }
        if (*p == ':') { addtok(TK_COLON, p, 1, line); p++; continue; }
        if (*p == '(') { addtok(TK_LP, p, 1, line); p++; continue; }
        if (*p == ')') { addtok(TK_RP, p, 1, line); p++; continue; }
        if (*p == '[') { addtok(TK_LB, p, 1, line); p++; continue; }
        if (*p == '{') { addtok(TK_LBRACE, p, 1, line); p++; continue; }
        if (*p == '.') { addtok(TK_DOT, p, 1, line); p++; continue; }
        if (*p == '}') { addtok(TK_RBRACE, p, 1, line); p++; continue; }
        if (*p == ']') { addtok(TK_RB, p, 1, line); p++; continue; }
        if (*p == '\\') { addtok(TK_LAM, p, 1, line); p++; continue; }
        if (*p == '|') { addtok(TK_BAR, p, 1, line); p++; continue; }
        if (*p == '~') { addtok(TK_TILDE, p, 1, line); p++; continue; }
        if (*p == ',') { addtok(TK_COMMA, p, 1, line); p++; continue; }
        if (isdigit((unsigned char)*p)) { const char *s = p; while (isdigit((unsigned char)*p)) p++; addtok(TK_NUM, s, (int)(p - s), line); continue; }
        if (isalpha((unsigned char)*p) || *p == '_') {
            const char *s = p; while (isident((unsigned char)*p)) p++;
            int n = (int)(p - s);
            #define KW(str, kind) if (n == (int)strlen(str) && !strncmp(s, str, n)) { addtok(kind, s, n, line); continue; }
            KW("def", TK_DEF) KW("data", TK_DATA) KW("where", TK_WHERE) KW("let", TK_LET) KW("in", TK_IN) KW("elim", TK_ELIM)
            KW("U", TK_U) KW("I", TK_I) KW("i0", TK_I0) KW("i1", TK_I1)
            KW("Level", TK_LEVEL) KW("lzero", TK_LZERO) KW("lsuc", TK_LSUC) KW("lmax", TK_LMAX) KW("mutual", TK_MUTUAL) KW("end", TK_END) KW("native", TK_NATIVE) KW("word", TK_WORD)
            KW("PathP", TK_PATHP) KW("Path", TK_PATH) KW("Partial", TK_PARTIAL) KW("transp", TK_TRANSP) KW("hcomp", TK_HCOMP) KW("comp", TK_COMP) KW("Sub", TK_SUB) KW("inS", TK_INS) KW("outS", TK_OUTS) KW("Sigma", TK_SIGMA) KW("fst", TK_FST) KW("snd", TK_SND) KW("Glue", TK_GLUE) KW("glue", TK_GLUEEL) KW("unglue", TK_UNGLUE)
            #undef KW
            addtok(TK_NAME, s, n, line); continue;
        }
        die("%s:%d: unexpected character '%c'", file, line, *p);
    }
    addtok(TK_EOF, p, 0, line);
}

static Tok *peek(void) { return &toks[pos]; }
static Tok *peekat(int k) { return pos + k < ntoks ? &toks[pos + k] : &toks[ntoks - 1]; }
static Tok *next(void) { Tok *t = &toks[pos]; if (t->k != TK_EOF) pos++; return t; }
static const char *tokname(TokKind k) {
    static const char *n[] = { "end of file", "name", "number", "'('", "')'", "'['", "']'", "':'", "':='", "'->'", "'\\'", "'|'",
                               "'~'", "'/\\'", "'\\/'",
                               "'def'", "'data'", "'where'", "'let'", "'in'", "'elim'", "'U'", "'I'", "'i0'", "'i1'",
                               "'PathP'", "'Path'", "'Partial'", "'transp'", "'hcomp'", "'comp'", "'Sub'", "'inS'", "'outS'", "','", "'Sigma'", "'fst'", "'snd'", "'Glue'", "'glue'", "'unglue'",
                               "'{'", "'}'", "'Level'", "'lzero'", "'lsuc'", "'lmax'", "'mutual'", "'end'", "'native'", "'word'", "'.'" };
    return n[k];
}
static Tok *expect(TokKind k) {
    Tok *t = peek();
    if (t->k != k) die("%s:%d: expected %s, found %s%s%.*s", file, t->line, tokname(k), tokname(t->k),
                       t->k == TK_NAME ? " " : "", t->k == TK_NAME ? t->n : 0, t->s);
    return next();
}
static const char *tokstr(Tok *t) { char *s = xalloc(t->n + 1); memcpy(s, t->s, t->n); s[t->n] = 0; return s; }

static STerm *st(SKind k, int line) { STerm *t = xalloc(sizeof *t); t->k = k; t->line = line; return t; }
static int binder_ahead(void) {
    int i = 0;
    if (peek()->k == TK_DOT) i = 1;   /* .(x : A): an irrelevant binder */
    if (peekat(i)->k != TK_LP && peekat(i)->k != TK_LBRACE) return 0;
    i++;
    if (peekat(i)->k != TK_NAME) return 0;
    while (peekat(i)->k == TK_NAME) i++;
    return peekat(i)->k == TK_COLON;
}
static int atom_ahead(void) {
    TokKind k = peek()->k;
    return k == TK_NAME || k == TK_NUM || k == TK_U || k == TK_ELIM || k == TK_LP || k == TK_LB || k == TK_LBRACE || k == TK_DOT || k == TK_I || k == TK_I0 || k == TK_I1 ||
           k == TK_LEVEL || k == TK_LZERO || k == TK_LSUC || k == TK_LMAX ||
           k == TK_PATHP || k == TK_PATH || k == TK_PARTIAL || k == TK_TRANSP || k == TK_HCOMP || k == TK_COMP || k == TK_SUB || k == TK_INS || k == TK_OUTS ||
           k == TK_SIGMA || k == TK_FST || k == TK_SND || k == TK_GLUE || k == TK_GLUEEL || k == TK_UNGLUE;
}
static STerm *wrap_pi(SBinder *b, int n, STerm *body) {
    for (int i = n - 1; i >= 0; i--) {
        STerm *r = st(S_PI, b[i].line); r->binders = &b[i]; r->nbinders = 1; r->a = body; body = r;
    }
    return body;
}
static STerm *wrap_lam(SBinder *b, int n, STerm *body) {
    for (int i = n - 1; i >= 0; i--) {
        STerm *r = st(S_LAM, b[i].line); r->binders = &b[i]; r->nbinders = 1; r->a = body; body = r;
    }
    return body;
}

/* ---- the parser on the machine (machine.h): each nonterminal a frame, its result through the register; the binders of a
   group live in the frame that collects them, their number in a register of the parser's own ---- */
static int pret_n;   /* parse_binders' count */
typedef struct { MHdr h; STerm *r, *a, *f; SBinder *b; int n, cap, imp, irrel, start; Tok *t; } PF;
#define F ((PF *)(mst.p + off))
#define MRETS(x) MRET((Val *)(void *)(x))
#define MST() ((STerm *)(void *)mret)
static void term_step(size_t off);
static void ior_step(size_t off);
static void iand_step(size_t off);
static void neg_step(size_t off);
static void app_step(size_t off);
static void atom_step(size_t off);
static void system_step(size_t off);
static void binders_step(size_t off);
static void ppush(void (*step)(size_t)) { mpush(sizeof(PF), step); }
static void binders_step(size_t off) {
    MSTART
    F->b = NULL; F->n = 0; F->cap = 0;
    while (binder_ahead()) {
        F->irrel = 0;
        if (peek()->k == TK_DOT) { next(); F->irrel = 1; }   /* .(x : A): irrelevant (M16b) */
        {   Tok *o = next(); F->imp = o->k == TK_LBRACE;   /* {x : A}: implicit */
            if (F->irrel && F->imp) die("%s:%d: a binder cannot be both irrelevant and implicit", file, o->line); }
        F->start = F->n;
        while (peek()->k == TK_NAME) {
            Tok *t = next();
            if (F->n == F->cap) { F->cap = F->cap ? 2 * F->cap : 4; F->b = rrealloc(F->b, F->cap * sizeof(SBinder)); }
            F->b[F->n].name = tokstr(t); F->b[F->n].ty = NULL; F->b[F->n].line = t->line; F->b[F->n].imp = F->imp; F->b[F->n].irrel = F->irrel; F->n++;
        }
        expect(TK_COLON);
        MCALL(ppush(term_step));
        for (int i = F->start; i < F->n; i++) F->b[i].ty = MST();
        expect(F->imp ? TK_RBRACE : TK_RP);
    }
    pret_n = F->n; MRETS(F->b);
    MFINISH
}
static void system_step(size_t off) {
    MSTART
    F->t = expect(TK_LB);
    F->r = st(S_SYS, F->t->line); F->cap = 0;
    while (peek()->k != TK_RB) {
        if (F->r->nbr) expect(TK_BAR);
        MCALL(ppush(ior_step)); F->a = MST();
        expect(TK_ARROW);
        MCALL(ppush(term_step));
        if (F->r->nbr == F->cap) { F->cap = F->cap ? 2 * F->cap : 4; F->r->br = rrealloc(F->r->br, F->cap * sizeof(SBranch)); }
        F->r->br[F->r->nbr].face = F->a; F->r->br[F->r->nbr].body = MST(); F->r->nbr++;
    }
    expect(TK_RB);
    MRETS(F->r);
    MFINISH
}
static void atom_step(size_t off) {
    MSTART
    F->t = peek();
    switch (F->t->k) {   /* the atoms that parse nothing below them (no resume point inside this switch) */
    case TK_NAME: { Tok *t = F->t; next(); if (t->n == 1 && t->s[0] == '_') MRETS(st(S_HOLE, t->line)); STerm *r = st(S_VAR, t->line); r->name = tokstr(t); MRETS(r); }
    case TK_NUM: {
        Tok *t = F->t; next(); STerm *r = st(S_NUM, t->line);
        r->digits = tokstr(t);
        errno = 0; r->num = strtoull(tokstr(t), NULL, 10);
        if (errno == ERANGE) r->num = ULLONG_MAX;   /* only a level needs the machine word; a literal of a data type is a bignum */
        MRETS(r); }
    case TK_LEVEL: next(); MRETS(st(S_LEVEL, F->t->line));
    case TK_LZERO: next(); MRETS(st(S_LZERO, F->t->line));
    case TK_I: next(); MRETS(st(S_I, F->t->line));
    case TK_I0: next(); MRETS(st(S_I0, F->t->line));
    case TK_I1: next(); MRETS(st(S_I1, F->t->line));
    case TK_PATHP: next(); MRETS(st(S_PATHP, F->t->line));
    case TK_PATH: { next(); STerm *r = st(S_PATHP, F->t->line); r->lvl = 1; MRETS(r); }   /* lvl=1 marks the non-dependent sugar */
    case TK_PARTIAL: next(); MRETS(st(S_PARTIAL, F->t->line));
    case TK_TRANSP: next(); MRETS(st(S_TRANSP, F->t->line));
    case TK_HCOMP: next(); MRETS(st(S_HCOMP, F->t->line));
    case TK_COMP: next(); MRETS(st(S_COMP, F->t->line));
    case TK_SUB: next(); MRETS(st(S_SUB, F->t->line));
    case TK_INS: next(); MRETS(st(S_INS, F->t->line));
    case TK_OUTS: next(); MRETS(st(S_OUTS, F->t->line));
    case TK_SIGMA: next(); MRETS(st(S_SIGMA, F->t->line));
    case TK_FST: next(); MRETS(st(S_FST, F->t->line));
    case TK_SND: next(); MRETS(st(S_SND, F->t->line));
    case TK_GLUE: next(); MRETS(st(S_GLUE, F->t->line));
    case TK_GLUEEL: next(); MRETS(st(S_GLUEEL, F->t->line));
    case TK_UNGLUE: next(); MRETS(st(S_UNGLUE, F->t->line));
    case TK_ELIM: { next(); Tok *d = expect(TK_NAME); STerm *r = st(S_ELIM, F->t->line); r->name = tokstr(d); MRETS(r); }
    case TK_LB: MBECOME(system_step);
    case TK_U: case TK_LBRACE: case TK_LSUC: case TK_LMAX: case TK_LP: break;
    default: die("%s:%d: expected a term, found %s", file, F->t->line, tokname(F->t->k));
    }
    if (F->t->k == TK_U) {
        next(); F->r = st(S_U, F->t->line); F->r->lvl = 0;
        if (peek()->k == TK_NUM) { Tok *n = next(); F->r->lvl = atoi(tokstr(n)); }
        else if (peek()->k == TK_LBRACE) { next(); MCALL(ppush(term_step)); F->r->a = MST(); expect(TK_RBRACE); }   /* U {l}: a level expression */
        MRETS(F->r);
    }
    if (F->t->k == TK_LBRACE) { next(); MCALL(ppush(term_step)); F->r = MST(); expect(TK_RBRACE); MRETS(F->r); }   /* {e}: a level argument, grouped */
    if (F->t->k == TK_LSUC) { next(); F->r = st(S_LSUC, F->t->line); MCALL(ppush(atom_step)); F->r->a = MST(); MRETS(F->r); }
    if (F->t->k == TK_LMAX) { next(); F->r = st(S_LMAX, F->t->line); MCALL(ppush(atom_step)); F->r->a = MST(); MCALL(ppush(atom_step)); F->r->b = MST(); MRETS(F->r); }
    /* TK_LP: a parenthesised term, or a pair (a , b) */
    next(); MCALL(ppush(term_step)); F->r = MST();
    if (peek()->k == TK_COMMA) { next(); F->a = st(S_PAIR, F->t->line); F->a->a = F->r; MCALL(ppush(term_step)); F->a->b = MST(); F->r = F->a; }
    expect(TK_RP); MRETS(F->r);
    MFINISH
}
static void app_step(size_t off) {
    MSTART
    MCALL(ppush(atom_step)); F->f = MST();
    while (atom_ahead()) {
        if ((peek()->k == TK_LP || peek()->k == TK_LBRACE) && binder_ahead()) break;
        if (peek()->k == TK_LB && in_con_type) break;
        F->imp = peek()->k == TK_LBRACE;   /* f {e}: e supplies the next implicit argument (a plain argument when there is none) */
        F->irrel = peek()->k == TK_DOT;    /* Sigma A .B: the second component is irrelevant */
        if (F->irrel) next();
        MCALL(ppush(atom_step));
        {   STerm *a = MST();
            if (F->imp) a->imp = 1;
            if (F->irrel) a->irrel = 1;
            STerm *r = st(S_APP, F->f->line); r->a = F->f; r->b = a; F->f = r; }
    }
    MRETS(F->f);
    MFINISH
}
static void neg_step(size_t off) {
    MSTART
    F->t = peek();
    if (F->t->k == TK_TILDE) { next(); F->r = st(S_INEG, F->t->line); MCALL(ppush(neg_step)); F->r->a = MST(); MRETS(F->r); }
    MBECOME(app_step);
    MFINISH
}
static void iand_step(size_t off) {
    MSTART
    MCALL(ppush(neg_step)); F->a = MST();
    while (peek()->k == TK_AND) { Tok *t = next(); F->r = st(S_IAND, t->line); F->r->a = F->a; MCALL(ppush(neg_step)); F->r->b = MST(); F->a = F->r; }
    MRETS(F->a);
    MFINISH
}
static void ior_step(size_t off) {
    MSTART
    MCALL(ppush(iand_step)); F->a = MST();
    while (peek()->k == TK_OR) { Tok *t = next(); F->r = st(S_IOR, t->line); F->r->a = F->a; MCALL(ppush(iand_step)); F->r->b = MST(); F->a = F->r; }
    MRETS(F->a);
    MFINISH
}
static void term_step(size_t off) {
    MSTART
    F->t = peek();
    if (F->t->k == TK_LAM) {
        next();
        F->b = NULL; F->n = 0; F->cap = 0;
        while (peek()->k == TK_NAME || (peek()->k == TK_LBRACE && peekat(1)->k == TK_NAME && peekat(2)->k == TK_RBRACE)) {
            int imp = peek()->k == TK_LBRACE; if (imp) next();   /* \{x}: an implicit lambda */
            Tok *x = next();
            if (imp) expect(TK_RBRACE);
            if (F->n == F->cap) { F->cap = F->cap ? 2 * F->cap : 4; F->b = rrealloc(F->b, F->cap * sizeof(SBinder)); }
            F->b[F->n].name = tokstr(x); F->b[F->n].ty = NULL; F->b[F->n].line = x->line; F->b[F->n].imp = imp; F->n++;
        }
        if (F->n == 0) die("%s:%d: lambda needs at least one binder", file, F->t->line);
        expect(TK_ARROW);
        MCALL(ppush(term_step));
        MRETS(wrap_lam(F->b, F->n, MST()));
    }
    if (F->t->k == TK_LET) {
        next(); { Tok *x = expect(TK_NAME); expect(TK_COLON); F->r = st(S_LET, F->t->line); F->r->name = tokstr(x); }
        MCALL(ppush(term_step)); F->r->a = MST(); expect(TK_DEFEQ);
        MCALL(ppush(term_step)); F->r->b = MST(); expect(TK_IN);
        MCALL(ppush(term_step)); F->r->c = MST();
        MRETS(F->r);
    }
    if (binder_ahead()) {
        MCALL(ppush(binders_step)); F->b = (SBinder *)(void *)mret; F->n = pret_n;
        expect(TK_ARROW);
        MCALL(ppush(term_step));
        MRETS(wrap_pi(F->b, F->n, MST()));
    }
    MCALL(ppush(ior_step)); F->a = MST();
    if (peek()->k == TK_ARROW) {
        next();
        MCALL(ppush(term_step));
        {   SBinder *b = xalloc(sizeof *b); b->name = "_"; b->ty = F->a; b->line = F->a->line;
            MRETS(wrap_pi(b, 1, MST())); }
    }
    MRETS(F->a);
    MFINISH
}
#undef F
/* the C entries (declarations call these; each runs the machine to its result) */
static STerm *parse_term(void) { ppush(term_step); return (STerm *)(void *)mrun(); }
static SBinder *parse_binders(int *n) { ppush(binders_step); SBinder *b = (SBinder *)(void *)mrun(); *n = pret_n; return b; }
static STerm *parse_system(void) { ppush(system_step); return (STerm *)(void *)mrun(); }

/* a data declaration after its 'data' token: name, parameters, index telescope, constructors */
static void parse_data_decl(SDecl *d) {
    d->isdata = 1; d->name = tokstr(expect(TK_NAME));
    d->params = parse_binders(&d->nparams);
    expect(TK_COLON); d->ty = parse_term();
    expect(TK_WHERE);
    int cap = 0;
    while (peek()->k == TK_BAR) {
        next(); Tok *c = expect(TK_NAME); expect(TK_COLON);
        if (d->ncons == cap) { cap = cap ? 2 * cap : 4; d->cons = rrealloc(d->cons, cap * sizeof(SCon)); }
        d->cons[d->ncons].name = tokstr(c); d->cons[d->ncons].line = c->line;
        in_con_type = 1; d->cons[d->ncons].ty = parse_term(); in_con_type = 0;
        d->cons[d->ncons].boundary = peek()->k == TK_LB ? parse_system() : NULL;   /* path constructor: its boundary */
        d->ncons++;
    }
}
SDecl *parse_program(const char *src, const char *fname) {
    file = fname; lex(src); pos = 0;
    SDecl *head = NULL, **tail = &head;
    while (peek()->k != TK_EOF) {
        Tok *t = next();
        SDecl *d = xalloc(sizeof *d); d->line = t->line;
        if (t->k == TK_DEF || t->k == TK_NATIVE || t->k == TK_WORD) {
            d->isnative = t->k == TK_NATIVE;
            d->isword = t->k == TK_WORD;
            d->name = tokstr(expect(TK_NAME));
            int n; SBinder *b = parse_binders(&n);
            expect(TK_COLON); STerm *ty = parse_term();
            expect(TK_DEFEQ); STerm *val = parse_term();
            d->ty = wrap_pi(b, n, ty); d->val = wrap_lam(b, n, val);
        } else if (t->k == TK_DATA) {
            parse_data_decl(d);
        } else if (t->k == TK_MUTUAL) {   /* a block: the binders are the parameters of every member */
            d->isdata = 2; d->params = parse_binders(&d->nparams); d->name = "mutual";
            int cap = 0;
            while (peek()->k == TK_DATA) {
                Tok *dt = next(); SDecl *m = xalloc(sizeof *m); m->line = dt->line;
                parse_data_decl(m);
                if (m->nparams) die("%s:%d: data %s in a mutual block: the parameters are declared on the block", file, m->line, m->name);
                if (d->nmembers == cap) { cap = cap ? 2 * cap : 4; d->members = rrealloc(d->members, cap * sizeof(SDecl *)); }
                d->members[d->nmembers++] = m;
            }
            if (d->nmembers == 0) die("%s:%d: an empty mutual block", file, t->line);
            expect(TK_END);
            if (d->nmembers == 1) { SDecl *m = d->members[0]; m->params = d->params; m->nparams = d->nparams; m->next = NULL; d = m; }   /* one member: a plain data type */
        } else die("%s:%d: expected 'def', 'native', 'word', 'data' or 'mutual', found %s", file, t->line, tokname(t->k));
        *tail = d; tail = &d->next;
    }
    return head;
}
