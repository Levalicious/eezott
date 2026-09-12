/*
 * parse.c - eezott lexer and recursive-descent parser.
 *
 *   program  := decl*
 *   decl     := 'def' name binder* ':' term ':=' term
 *             | 'data' name binder* ':' term 'where' ('|' name ':' term)*
 *   binder   := '(' name+ ':' term ')'
 *   term     := binder+ '->' term            dependent function type
 *             | '\' name+ '->' term          lambda
 *             | 'let' name ':' term ':=' term 'in' term
 *             | app ('->' term)?             non-dependent arrow
 *   app      := atom atom*
 *   atom     := name | 'U' [0-9]+? | 'elim' name | '(' term ')'
 *   comments: '#' or '--' to end of line.
 */
#include "tt.h"
#include <ctype.h>

typedef enum { TK_EOF, TK_NAME, TK_NUM, TK_LP, TK_RP, TK_COLON, TK_DEFEQ, TK_ARROW, TK_LAM, TK_BAR,
               TK_DEF, TK_DATA, TK_WHERE, TK_LET, TK_IN, TK_ELIM, TK_U } TokKind;
typedef struct { TokKind k; const char *s; int n; int line; } Tok;

static Tok *toks; static int ntoks, tcap, pos; static const char *file;

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
        if (*p == ':') { addtok(TK_COLON, p, 1, line); p++; continue; }
        if (*p == '(') { addtok(TK_LP, p, 1, line); p++; continue; }
        if (*p == ')') { addtok(TK_RP, p, 1, line); p++; continue; }
        if (*p == '\\') { addtok(TK_LAM, p, 1, line); p++; continue; }
        if (*p == '|') { addtok(TK_BAR, p, 1, line); p++; continue; }
        if (isdigit((unsigned char)*p)) { const char *s = p; while (isdigit((unsigned char)*p)) p++; addtok(TK_NUM, s, (int)(p - s), line); continue; }
        if (isalpha((unsigned char)*p) || *p == '_') {
            const char *s = p; while (isident((unsigned char)*p)) p++;
            int n = (int)(p - s);
            #define KW(str, kind) if (n == (int)strlen(str) && !strncmp(s, str, n)) { addtok(kind, s, n, line); continue; }
            KW("def", TK_DEF) KW("data", TK_DATA) KW("where", TK_WHERE) KW("let", TK_LET) KW("in", TK_IN) KW("elim", TK_ELIM) KW("U", TK_U)
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
    static const char *n[] = { "end of file", "name", "number", "'('", "')'", "':'", "':='", "'->'", "'\\'", "'|'",
                               "'def'", "'data'", "'where'", "'let'", "'in'", "'elim'", "'U'" };
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

/* binder group: '(' name+ ':' term ')'  -- caller has verified the shape */
static int binder_ahead(void) {
    if (peek()->k != TK_LP) return 0;
    int i = 1;
    if (peekat(i)->k != TK_NAME) return 0;
    while (peekat(i)->k == TK_NAME) i++;
    return peekat(i)->k == TK_COLON;
}
static void parse_binder_group(SBinder **out, int *n, int *cap) {
    expect(TK_LP);
    int start = *n;
    while (peek()->k == TK_NAME) {
        Tok *t = next();
        if (*n == *cap) { *cap = *cap ? 2 * *cap : 4; *out = realloc(*out, *cap * sizeof(SBinder)); if (!*out) die("out of memory"); }
        (*out)[*n].name = tokstr(t); (*out)[*n].ty = NULL; (*out)[*n].line = t->line; (*n)++;
    }
    expect(TK_COLON);
    STerm *ty = parse_term();
    for (int i = start; i < *n; i++) (*out)[i].ty = ty;
    expect(TK_RP);
}
static SBinder *parse_binders(int *n) {
    SBinder *b = NULL; int cap = 0; *n = 0;
    while (binder_ahead()) parse_binder_group(&b, n, &cap);
    return b;
}

static STerm *parse_atom(void) {
    Tok *t = peek();
    switch (t->k) {
    case TK_NAME: { next(); STerm *r = st(S_VAR, t->line); r->name = tokstr(t); return r; }
    case TK_U: { next(); STerm *r = st(S_U, t->line); r->lvl = 0;
                 if (peek()->k == TK_NUM) { Tok *n = next(); r->lvl = atoi(tokstr(n)); } return r; }
    case TK_ELIM: { next(); Tok *d = expect(TK_NAME); STerm *r = st(S_ELIM, t->line); r->name = tokstr(d); return r; }
    case TK_LP: { next(); STerm *r = parse_term(); expect(TK_RP); return r; }
    default: die("%s:%d: expected a term, found %s", file, t->line, tokname(t->k));
    }
    return NULL;
}
static int atom_ahead(void) { TokKind k = peek()->k; return k == TK_NAME || k == TK_U || k == TK_ELIM || k == TK_LP; }

static STerm *parse_app(void) {
    STerm *f = parse_atom();
    while (atom_ahead()) {
        if (peek()->k == TK_LP && binder_ahead()) break;
        STerm *a = parse_atom();
        STerm *r = st(S_APP, f->line); r->a = f; r->b = a; f = r;
    }
    return f;
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
        while (peek()->k == TK_NAME) {
            Tok *x = next();
            if (n == cap) { cap = cap ? 2 * cap : 4; b = realloc(b, cap * sizeof(SBinder)); if (!b) die("out of memory"); }
            b[n].name = tokstr(x); b[n].ty = NULL; b[n].line = x->line; n++;
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
    STerm *a = parse_app();
    if (peek()->k == TK_ARROW) {
        next();
        STerm *body = parse_term();
        SBinder *b = xalloc(sizeof *b); b->name = "_"; b->ty = a; b->line = a->line;
        return wrap_pi(b, 1, body);
    }
    return a;
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
            d->isdata = 1; d->name = tokstr(expect(TK_NAME));
            d->params = parse_binders(&d->nparams);
            expect(TK_COLON); d->ty = parse_term();
            expect(TK_WHERE);
            int cap = 0;
            while (peek()->k == TK_BAR) {
                next(); Tok *c = expect(TK_NAME); expect(TK_COLON);
                if (d->ncons == cap) { cap = cap ? 2 * cap : 4; d->cons = realloc(d->cons, cap * sizeof(SCon)); if (!d->cons) die("out of memory"); }
                d->cons[d->ncons].name = tokstr(c); d->cons[d->ncons].line = c->line; d->cons[d->ncons].ty = parse_term(); d->ncons++;
            }
        } else die("%s:%d: expected 'def' or 'data', found %s", file, t->line, tokname(t->k));
        *tail = d; tail = &d->next;
    }
    return head;
}
