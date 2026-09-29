/*
 * machine.h - the explicit machine (S3) shared by the evaluator (eval.c) and the elaborator (elab.c): frames on one heap
 * stack, a driver loop, and the step macros. A step file defines F as its frame at offset off before using the macros;
 * resume points are numbered by __COUNTER__ (unique within a file).
 */
#ifndef EEZOTT_MACHINE_H
#define EEZOTT_MACHINE_H
#include "tt.h"
typedef struct { void (*step)(size_t); int pc; size_t prev; } MHdr;
extern Stack mst; extern size_t mtop; extern Val *mret;
static inline void *mpush(size_t size, void (*step)(size_t)) {
    size = (size + 15) & ~(size_t)15;
    size_t off = (mst.n + 15) & ~(size_t)15;
    stack_reserve(&mst, off + size);
    mst.n = off + size;
    MHdr *h = (MHdr *)(mst.p + off);
    memset(h, 0, size);
    h->step = step; h->prev = mtop;
    mtop = off;
    return h;
}
static inline void mpop(size_t off) { mtop = ((MHdr *)(mst.p + off))->prev; mst.n = off; }
/* run the frame just pushed, and all it calls, to its value */
static inline Val *mrun(void) {
    size_t below = ((MHdr *)(mst.p + mtop))->prev;
    while (mtop != below) { size_t off = mtop; ((MHdr *)(mst.p + off))->step(off); }
    return mret;
}
#define MSTART switch (F->h.pc) { case 0:;
#define MFINISH } return;
#define MCALL(push) MCALL_((push), __COUNTER__ + 1)   /* a resume point: a number unique in the file, never 0 */
#define MCALL_(push, n) do { F->h.pc = (n); push; return; case (n):; } while (0)
#define MRET(v) do { Val *mr_ = (v); mret = mr_; mpop(off); return; } while (0)
#define MTAIL(push) do { mpop(off); push; return; } while (0)   /* the callee's value is this frame's: its caller resumes */
#define MBECOME(st) do { F->h.step = (st); F->h.pc = 0; return; } while (0)
#define MRETT(t) MRET((Val *)(void *)(t))   /* a term result through the register */
#define MTERM() ((Term *)(void *)mret)
#endif
