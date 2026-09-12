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

static LVal lv_norm(LVal a) {
    for (int i = 1; i < a.n; i++) {   /* sort by variable */
        LAtom x = a.t[i]; int j = i - 1;
        while (j >= 0 && a.t[j].var > x.var) { a.t[j + 1] = a.t[j]; j--; }
        a.t[j + 1] = x;
    }
    int m = 0;   /* merge a variable's summands by the larger offset */
    for (int i = 0; i < a.n; i++) {
        if (m > 0 && a.t[m - 1].var == a.t[i].var) { if (a.t[i].off > a.t[m - 1].off) a.t[m - 1].off = a.t[i].off; }
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
LVal lv_var(int level) { LVal a = { 0, xalloc(sizeof(LAtom)), 1 }; a.t[0].var = level; a.t[0].off = 0; return a; }
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
    for (int i = 0; i < a.n; i++) if (a.t[i].var != b.t[i].var || a.t[i].off != b.t[i].off) return 0;
    return 1;
}
int lv_leq(LVal a, LVal b) {
    for (int i = 0; i < a.n; i++) {
        int ok = 0;
        for (int j = 0; j < b.n; j++) if (b.t[j].var == a.t[i].var && b.t[j].off >= a.t[i].off) { ok = 1; break; }
        if (!ok) return 0;
    }
    if (a.c == 0 || a.c <= b.c) return 1;
    for (int j = 0; j < b.n; j++) if (b.t[j].off >= a.c) return 1;
    return 0;
}
LVal lv_subst(LVal a, int var, LVal s) {
    LVal r = lv_const(a.c);
    for (int i = 0; i < a.n; i++) {
        if (a.t[i].var == var) r = lv_max(r, lv_add(s, a.t[i].off));
        else { LVal one = lv_var(a.t[i].var); one.t[0].off = a.t[i].off; r = lv_max(r, one); }
    }
    return r;
}
