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
#include <ctype.h>
#include <errno.h>

typedef enum { TK_EOF, TK_NAME, TK_NUM, TK_LP, TK_RP, TK_LB, TK_RB, TK_COLON, TK_DEFEQ, TK_ARROW, TK_LAM, TK_BAR,
               TK_TILDE, TK_AND, TK_OR,
               TK_DEF, TK_DATA, TK_WHERE, TK_LET, TK_IN, TK_ELIM, TK_U, TK_I, TK_I0, TK_I1,
               TK_PATHP, TK_PATH, TK_PARTIAL, TK_TRANSP, TK_HCOMP, TK_COMP, TK_SUB, TK_INS, TK_OUTS,
               TK_COMMA, TK_SIGMA, TK_FST, TK_SND, TK_GLUE, TK_GLUEEL, TK_UNGLUE,
               TK_LBRACE, TK_RBRACE, TK_LEVEL, TK_LZERO, TK_LSUC, TK_LMAX, TK_MUTUAL, TK_END } TokKind;
typedef struct { TokKind k; const char *s; int n; int line; } Tok;

static Tok *toks; static int ntoks, tcap, pos; static const char *file;
static int in_con_type;   /* while parsing a constructor's type: a following system is its boundary, not an argument */

static void addtok(TokKind k, const char *s, int n, int line) {
    if (ntoks == tcap) { tcap = tcap ? 2 * tcap : 256; toks = realloc(toks, tcap * sizeof(Tok)); if (!toks) die("out of memory"); }
    Tok *t = &toks[ntoks++]; t->k = k; t->s = s; t->n = n; t->line = line;
}
static int isident(int c) { return isalnum(c) || c == '_' || c == '\''; }

static void lex(const char *src) {
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
            KW("Level", TK_LEVEL) KW("lzero", TK_LZERO) KW("lsuc", TK_LSUC) KW("lmax", TK_LMAX) KW("mutual", TK_MUTUAL) KW("end", TK_END)
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
                               "'{'", "'}'", "'Level'", "'lzero'", "'lsuc'", "'lmax'", "'mutual'", "'end'" };
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
static STerm *parse_term(void);
static STerm *parse_ior(void);

static int binder_ahead(void) {
    if (peek()->k != TK_LP && peek()->k != TK_LBRACE) return 0;
    int i = 1;
    if (peekat(i)->k != TK_NAME) return 0;
    while (peekat(i)->k == TK_NAME) i++;
    return peekat(i)->k == TK_COLON;
}
static void parse_binder_group(SBinder **out, int *n, int *cap) {
    Tok *o = next(); int imp = o->k == TK_LBRACE;   /* {x : A}: implicit */
    int start = *n;
    while (peek()->k == TK_NAME) {
        Tok *t = next();
        if (*n == *cap) { *cap = *cap ? 2 * *cap : 4; *out = realloc(*out, *cap * sizeof(SBinder)); if (!*out) die("out of memory"); }
        (*out)[*n].name = tokstr(t); (*out)[*n].ty = NULL; (*out)[*n].line = t->line; (*out)[*n].imp = imp; (*n)++;
    }
    expect(TK_COLON);
    STerm *ty = parse_term();
    for (int i = start; i < *n; i++) (*out)[i].ty = ty;
    expect(imp ? TK_RBRACE : TK_RP);
}
static SBinder *parse_binders(int *n) {
    SBinder *b = NULL; int cap = 0; *n = 0;
    while (binder_ahead()) parse_binder_group(&b, n, &cap);
    return b;
}

static STerm *parse_system(void) {
    Tok *t = expect(TK_LB);
    STerm *r = st(S_SYS, t->line);
    int cap = 0;
    while (peek()->k != TK_RB) {
        if (r->nbr) expect(TK_BAR);
        STerm *face = parse_ior();
        expect(TK_ARROW);
        STerm *body = parse_term();
        if (r->nbr == cap) { cap = cap ? 2 * cap : 4; r->br = realloc(r->br, cap * sizeof(SBranch)); if (!r->br) die("out of memory"); }
        r->br[r->nbr].face = face; r->br[r->nbr].body = body; r->nbr++;
    }
    expect(TK_RB);
    return r;
}

static STerm *parse_atom(void) {
    Tok *t = peek();
    switch (t->k) {
    case TK_NAME: { next(); if (t->n == 1 && t->s[0] == '_') return st(S_HOLE, t->line); STerm *r = st(S_VAR, t->line); r->name = tokstr(t); return r; }
    case TK_NUM: {
        next(); STerm *r = st(S_NUM, t->line);
        errno = 0; r->num = strtoull(tokstr(t), NULL, 10);
        if (errno == ERANGE) die("%s:%d: the numeral %s is too large", file, t->line, tokstr(t));
        return r; }
    case TK_U: { next(); STerm *r = st(S_U, t->line); r->lvl = 0;
                 if (peek()->k == TK_NUM) { Tok *n = next(); r->lvl = atoi(tokstr(n)); }
                 else if (peek()->k == TK_LBRACE) { next(); r->a = parse_term(); expect(TK_RBRACE); }   /* U {l}: a level expression */
                 return r; }
    case TK_LBRACE: { next(); STerm *r = parse_term(); expect(TK_RBRACE); return r; }   /* {e}: a level argument, grouped */
    case TK_LEVEL: next(); return st(S_LEVEL, t->line);
    case TK_LZERO: next(); return st(S_LZERO, t->line);
    case TK_LSUC: { next(); STerm *r = st(S_LSUC, t->line); r->a = parse_atom(); return r; }
    case TK_LMAX: { next(); STerm *r = st(S_LMAX, t->line); r->a = parse_atom(); r->b = parse_atom(); return r; }
    case TK_I: next(); return st(S_I, t->line);
    case TK_I0: next(); return st(S_I0, t->line);
    case TK_I1: next(); return st(S_I1, t->line);
    case TK_PATHP: next(); return st(S_PATHP, t->line);
    case TK_PATH: { next(); STerm *r = st(S_PATHP, t->line); r->lvl = 1; return r; }   /* lvl=1 marks the non-dependent sugar */
    case TK_PARTIAL: next(); return st(S_PARTIAL, t->line);
    case TK_TRANSP: next(); return st(S_TRANSP, t->line);
    case TK_HCOMP: next(); return st(S_HCOMP, t->line);
    case TK_COMP: next(); return st(S_COMP, t->line);
    case TK_SUB: next(); return st(S_SUB, t->line);
    case TK_INS: next(); return st(S_INS, t->line);
    case TK_OUTS: next(); return st(S_OUTS, t->line);
    case TK_SIGMA: next(); return st(S_SIGMA, t->line);
    case TK_FST: next(); return st(S_FST, t->line);
    case TK_SND: next(); return st(S_SND, t->line);
    case TK_GLUE: next(); return st(S_GLUE, t->line);
    case TK_GLUEEL: next(); return st(S_GLUEEL, t->line);
    case TK_UNGLUE: next(); return st(S_UNGLUE, t->line);
    case TK_ELIM: { next(); Tok *d = expect(TK_NAME); STerm *r = st(S_ELIM, t->line); r->name = tokstr(d); return r; }
    case TK_LP: {   /* parenthesised term, or a pair (a , b) */
        next(); STerm *r = parse_term();
        if (peek()->k == TK_COMMA) { next(); STerm *q = st(S_PAIR, t->line); q->a = r; q->b = parse_term(); r = q; }
        expect(TK_RP); return r; }
    case TK_LB: return parse_system();
    default: die("%s:%d: expected a term, found %s", file, t->line, tokname(t->k));
    }
    return NULL;
}
static int atom_ahead(void) {
    TokKind k = peek()->k;
    return k == TK_NAME || k == TK_NUM || k == TK_U || k == TK_ELIM || k == TK_LP || k == TK_LB || k == TK_LBRACE || k == TK_I || k == TK_I0 || k == TK_I1 ||
           k == TK_LEVEL || k == TK_LZERO || k == TK_LSUC || k == TK_LMAX ||
           k == TK_PATHP || k == TK_PATH || k == TK_PARTIAL || k == TK_TRANSP || k == TK_HCOMP || k == TK_COMP || k == TK_SUB || k == TK_INS || k == TK_OUTS ||
           k == TK_SIGMA || k == TK_FST || k == TK_SND || k == TK_GLUE || k == TK_GLUEEL || k == TK_UNGLUE;
}

static STerm *parse_app(void) {
    STerm *f = parse_atom();
    while (atom_ahead()) {
        if ((peek()->k == TK_LP || peek()->k == TK_LBRACE) && binder_ahead()) break;
        if (peek()->k == TK_LB && in_con_type) break;
        int imp = peek()->k == TK_LBRACE;   /* f {e}: e supplies the next implicit argument (a plain argument when there is none) */
        STerm *a = parse_atom();
        if (imp) a->imp = 1;
        STerm *r = st(S_APP, f->line); r->a = f; r->b = a; f = r;
    }
    return f;
}
static STerm *parse_neg(void) {
    Tok *t = peek();
    if (t->k == TK_TILDE) { next(); STerm *r = st(S_INEG, t->line); r->a = parse_neg(); return r; }
    return parse_app();
}
static STerm *parse_iand(void) {
    STerm *a = parse_neg();
    while (peek()->k == TK_AND) { Tok *t = next(); STerm *r = st(S_IAND, t->line); r->a = a; r->b = parse_neg(); a = r; }
    return a;
}
static STerm *parse_ior(void) {
    STerm *a = parse_iand();
    while (peek()->k == TK_OR) { Tok *t = next(); STerm *r = st(S_IOR, t->line); r->a = a; r->b = parse_iand(); a = r; }
    return a;
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

static STerm *parse_term(void) {
    Tok *t = peek();
    if (t->k == TK_LAM) {
        next();
        SBinder *b = NULL; int n = 0, cap = 0;
        while (peek()->k == TK_NAME || (peek()->k == TK_LBRACE && peekat(1)->k == TK_NAME && peekat(2)->k == TK_RBRACE)) {
            int imp = peek()->k == TK_LBRACE; if (imp) next();   /* \{x}: an implicit lambda */
            Tok *x = next();
            if (imp) expect(TK_RBRACE);
            if (n == cap) { cap = cap ? 2 * cap : 4; b = realloc(b, cap * sizeof(SBinder)); if (!b) die("out of memory"); }
            b[n].name = tokstr(x); b[n].ty = NULL; b[n].line = x->line; b[n].imp = imp; n++;
        }
        if (n == 0) die("%s:%d: lambda needs at least one binder", file, t->line);
        expect(TK_ARROW);
        return wrap_lam(b, n, parse_term());
    }
    if (t->k == TK_LET) {
        next(); Tok *x = expect(TK_NAME); expect(TK_COLON);
        STerm *r = st(S_LET, t->line); r->name = tokstr(x);
        r->a = parse_term(); expect(TK_DEFEQ); r->b = parse_term(); expect(TK_IN); r->c = parse_term();
        return r;
    }
    if (binder_ahead()) {
        int n; SBinder *b = parse_binders(&n);
        expect(TK_ARROW);
        return wrap_pi(b, n, parse_term());
    }
    STerm *a = parse_ior();
    if (peek()->k == TK_ARROW) {
        next();
        STerm *body = parse_term();
        SBinder *b = xalloc(sizeof *b); b->name = "_"; b->ty = a; b->line = a->line;
        return wrap_pi(b, 1, body);
    }
    return a;
}

/* a data declaration after its 'data' token: name, parameters, index telescope, constructors */
static void parse_data_decl(SDecl *d) {
    d->isdata = 1; d->name = tokstr(expect(TK_NAME));
    d->params = parse_binders(&d->nparams);
    expect(TK_COLON); d->ty = parse_term();
    expect(TK_WHERE);
    int cap = 0;
    while (peek()->k == TK_BAR) {
        next(); Tok *c = expect(TK_NAME); expect(TK_COLON);
        if (d->ncons == cap) { cap = cap ? 2 * cap : 4; d->cons = realloc(d->cons, cap * sizeof(SCon)); if (!d->cons) die("out of memory"); }
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
        if (t->k == TK_DEF) {
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
                if (d->nmembers == cap) { cap = cap ? 2 * cap : 4; d->members = realloc(d->members, cap * sizeof(SDecl *)); if (!d->members) die("out of memory"); }
                d->members[d->nmembers++] = m;
            }
            if (d->nmembers == 0) die("%s:%d: an empty mutual block", file, t->line);
            expect(TK_END);
            if (d->nmembers == 1) { SDecl *m = d->members[0]; m->params = d->params; m->nparams = d->nparams; m->next = NULL; d = m; }   /* one member: a plain data type */
        } else die("%s:%d: expected 'def', 'data' or 'mutual', found %s", file, t->line, tokname(t->k));
        *tail = d; tail = &d->next;
    }
    return head;
}
