/* level.c: universe levels as values.
 *
 * A level is an element of the free max-plus algebra on the context's level
 * variables, kept in normal form max(c, l_1 + n_1, ..., l_k + n_k): each
 * variable (by de Bruijn level) at most once, sorted, with its largest
 * offset; the constant c kept only when no summand dominates it (c > every
 * n_i), and 0 otherwise. Normal forms are unique, so equality is
 * structural, and a <= b is decided summand by summand: variables are
 * natural numbers, so l + n >= n dominates every constant c <= n.
 */
#include "tt.h"
#include <string.h>

static int atom_lt(LAtom a, LAtom b) { return a.meta != b.meta ? a.meta < b.meta : a.var < b.var; }
static int atom_same(LAtom a, LAtom b) { return a.meta == b.meta && a.var == b.var; }
static LVal lv_norm(LVal a) {
    for (int i = 1; i < a.n; i++) {   /* sort by variable (rigid ones first) */
        LAtom x = a.t[i]; int j = i - 1;
        while (j >= 0 && atom_lt(x, a.t[j])) { a.t[j + 1] = a.t[j]; j--; }
        a.t[j + 1] = x;
    }
    int m = 0;   /* merge a variable's summands by the larger offset */
    for (int i = 0; i < a.n; i++) {
        if (m > 0 && atom_same(a.t[m - 1], a.t[i])) { if (a.t[i].off > a.t[m - 1].off) a.t[m - 1].off = a.t[i].off; }
        else a.t[m++] = a.t[i];
    }
    a.n = m;
    int mo = -1; for (int i = 0; i < a.n; i++) if (a.t[i].off > mo) mo = a.t[i].off;
    if (a.n > 0 && a.c <= mo) a.c = 0;   /* the constant is dominated */
    return a;
}
static LVal lv_copy(LVal a) {
    LVal r = a; r.t = xalloc((a.n + 1) * sizeof(LAtom));
    if (a.n) memcpy(r.t, a.t, a.n * sizeof(LAtom));
    return r;
}
LVal lv_const(int n) { LVal a = { n, NULL, 0 }; return a; }
LVal lv_var(int level) { LVal a = { 0, xalloc(sizeof(LAtom)), 1 }; a.t[0].var = level; a.t[0].off = 0; a.t[0].meta = 0; return a; }
LVal lv_meta(int id) { LVal a = { 0, xalloc(sizeof(LAtom)), 1 }; a.t[0].var = id; a.t[0].off = 0; a.t[0].meta = 1; return a; }
int lv_has_meta(LVal a) { for (int i = 0; i < a.n; i++) if (a.t[i].meta) return 1; return 0; }
LVal lv_add(LVal a, int k) {
    LVal r = lv_copy(a);
    for (int i = 0; i < r.n; i++) r.t[i].off += k;
    r.c = (a.n == 0 || a.c > 0) ? a.c + k : 0;   /* a dominated constant stays dominated */
    return lv_norm(r);
}
LVal lv_max(LVal a, LVal b) {
    LVal r; r.n = a.n + b.n; r.t = xalloc((r.n + 1) * sizeof(LAtom));
    if (a.n) memcpy(r.t, a.t, a.n * sizeof(LAtom));
    if (b.n) memcpy(r.t + a.n, b.t, b.n * sizeof(LAtom));
    r.c = a.c > b.c ? a.c : b.c;
    return lv_norm(r);
}
int lv_is_const(LVal a, int *n) { if (a.n) return 0; *n = a.c; return 1; }
int lv_eq(LVal a, LVal b) {
    if (a.c != b.c || a.n != b.n) return 0;
    for (int i = 0; i < a.n; i++) if (!atom_same(a.t[i], b.t[i]) || a.t[i].off != b.t[i].off) return 0;
    return 1;
}
int lv_leq(LVal a, LVal b) {
    for (int i = 0; i < a.n; i++) {
        int ok = 0;
        for (int j = 0; j < b.n; j++) if (atom_same(b.t[j], a.t[i]) && b.t[j].off >= a.t[i].off) { ok = 1; break; }
        if (!ok) return 0;
    }
    if (a.c == 0 || a.c <= b.c) return 1;
    for (int j = 0; j < b.n; j++) if (b.t[j].off >= a.c) return 1;
    return 0;
}
static LVal subst_atom(LVal a, int meta, int id, LVal s) {
    LVal r = lv_const(a.c);
    for (int i = 0; i < a.n; i++) {
        if (a.t[i].meta == meta && a.t[i].var == id) r = lv_max(r, lv_add(s, a.t[i].off));
        else { LVal one = a.t[i].meta ? lv_meta(a.t[i].var) : lv_var(a.t[i].var); one.t[0].off = a.t[i].off; r = lv_max(r, one); }
    }
    return r;
}
LVal lv_subst(LVal a, int var, LVal s) { return subst_atom(a, 0, var, s); }
LVal lv_subst_meta(LVal a, int id, LVal s) { return subst_atom(a, 1, id, s); }

/* ---------------- the constraint store ---------------- */

/* nodes: kind 0 = the constant 0 (id 0), 1 = a rigid variable (de Bruijn level), 2 = a meta (id) */
typedef struct { int xk, x, yk, y, k; } LEdge;      /* y >= x + k */
typedef struct { LVal a, b; } LDefer;                /* a <= b deferred: a is a single meta summand, b a max of several */
static LEdge *edges; static int nedges, capedges;
static LDefer *defers; static int ndefers, capdefers;
static int nmetas;

LMark lstore_mark(void) { LMark m = { nedges, ndefers }; return m; }
void lstore_rollback(LMark m) { nedges = m.e; ndefers = m.d; }
int lv_meta_new(void) { return nmetas++; }
int lstore_nedges(void) { return nedges; }
int lstore_ndeferred(void) { return ndefers; }

static int node_kind(LAtom t) { return t.meta ? 2 : 1; }
/* the longest path from (xk,x) to (yk,y) through the edges and the implicit 0 -> v edges; INT_MIN if none.
   The store has no positive cycles, so |V| rounds of relaxation suffice. */
#define NEG (-1000000000)
static int longest(int xk, int x, int yk, int y) {
    if (xk == yk && x == y) return 0;
    /* collect the nodes */
    int cap = 2 * nedges + 4, nn = 0; int *nk = xalloc(cap * sizeof(int)), *ni = xalloc(cap * sizeof(int)), *d = xalloc(cap * sizeof(int));
    #define NODE(kk, ii) ({ int f_ = -1; for (int q = 0; q < nn; q++) if (nk[q] == (kk) && ni[q] == (ii)) { f_ = q; break; } \
                            if (f_ < 0) { nk[nn] = (kk); ni[nn] = (ii); d[nn] = NEG; f_ = nn++; } f_; })
    int s = NODE(xk, x), t = NODE(yk, y), z = NODE(0, 0);
    for (int i = 0; i < nedges; i++) { NODE(edges[i].xk, edges[i].x); NODE(edges[i].yk, edges[i].y); }
    d[s] = 0;
    for (int round = 0; round < nn + 1; round++) {
        int changed = 0;
        if (d[z] > NEG) for (int q = 0; q < nn; q++) if (nk[q] != 0 && d[z] > d[q]) { d[q] = d[z]; changed = 1; }   /* every variable >= 0 */
        for (int i = 0; i < nedges; i++) {
            int a = NODE(edges[i].xk, edges[i].x), b = NODE(edges[i].yk, edges[i].y);
            if (d[a] > NEG && d[a] + edges[i].k > d[b]) { d[b] = d[a] + edges[i].k; changed = 1; }
        }
        if (!changed) break;
    }
    #undef NODE
    return d[t];
}
/* is y >= x + k derivable? */
static int derivable(int xk, int x, int yk, int y, int k) {
    if (xk == 0 && yk == 0) return k <= 0;
    int l = longest(xk, x, yk, y);
    return l > NEG && l >= k;
}
/* add y >= x + k; 0 if it would close a positive cycle */
static int add_edge(int xk, int x, int yk, int y, int k) {
    if (derivable(xk, x, yk, y, k)) return 1;
    if (xk != 2 && yk != 2) return 0;   /* rigid variables and constants take no new constraints: only derivable ones hold */
    int back = longest(yk, y, xk, x);   /* a path y -> x of weight w closes a cycle of weight k + w */
    if (back > NEG && k + back > 0) return 0;
    if (nedges == capedges) { capedges = capedges ? 2 * capedges : 64; LEdge *ne = xalloc(capedges * sizeof(LEdge)); if (nedges) memcpy(ne, edges, nedges * sizeof(LEdge)); edges = ne; }
    LEdge e = { xk, x, yk, y, k }; edges[nedges++] = e;
    return 1;
}
/* summand s (an atom, or the constant when t == NULL) below a single summand of b */
static int summand_leq(const LAtom *s, int sc, const LAtom *t, int tc, int add) {
    int xk = s ? node_kind(*s) : 0, x = s ? s->var : 0, xo = s ? s->off : sc;
    int yk = t ? node_kind(*t) : 0, y = t ? t->var : 0, yo = t ? t->off : tc;
    /* x + xo <= y + yo  <=>  y >= x + (xo - yo) */
    return add ? add_edge(xk, x, yk, y, xo - yo) : derivable(xk, x, yk, y, xo - yo);
}
int lv_enforce_leq(LVal a, LVal b) {
    int nb = b.n + (b.c > 0 || b.n == 0 ? 1 : 0);   /* summands of b: its atoms, and its constant when it is not dominated */
    int na = a.n + (a.c > 0 || a.n == 0 ? 1 : 0);
    for (int i = 0; i < na; i++) {
        const LAtom *s = i < a.n ? &a.t[i] : NULL;
        if (nb == 1) {   /* a single summand: an edge */
            const LAtom *t = b.n ? &b.t[0] : NULL;
            if (!summand_leq(s, a.c, t, b.c, 1)) return 0;
            continue;
        }
        if (s && s->meta) {   /* a meta below a max of several: decided once the meta is solved */
            if (ndefers == capdefers) { capdefers = capdefers ? 2 * capdefers : 16; LDefer *nd = xalloc(capdefers * sizeof(LDefer)); if (ndefers) memcpy(nd, defers, ndefers * sizeof(LDefer)); defers = nd; }
            LVal one = lv_meta(s->var); one.t[0].off = s->off;
            LDefer df = { one, b }; defers[ndefers++] = df;
            continue;
        }
        int ok = 0;   /* rigid or constant: some choice must already be derivable */
        for (int j = 0; j < nb && !ok; j++) ok = summand_leq(s, a.c, j < b.n ? &b.t[j] : NULL, b.c, 0);
        if (!ok) return -1;
    }
    return 1;
}
int lv_enforce_eq(LVal a, LVal b) {
    if (lv_eq(a, b)) return 1;
    int r = lv_enforce_leq(a, b); if (r != 1) return r;
    return lv_enforce_leq(b, a);
}
