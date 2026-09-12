/*
 * main.c - eezott driver.
 *
 *   eezott [-c] [-K] [FILE]   check FILE (or stdin); unless -c, write the erased eezoc source to stdout
 *   -K keeps every Kan operation at run time (no identity shortcut for constant lines): a differential test of the run-time rules
 *
 * The output is meant to be piped straight into eezoc:
 *   eezott prog.tt | eezoc | eezo
 */
#include "tt.h"

static char *slurp(FILE *f) {
    size_t cap = 1 << 16, n = 0; char *buf = xalloc(cap);
    for (;;) {
        size_t r = fread(buf + n, 1, cap - n - 1, f);
        n += r;
        if (n + 1 < cap) break;
        char *nb = xalloc(cap * 2); memcpy(nb, buf, n); buf = nb; cap *= 2;
    }
    buf[n] = 0; return buf;
}

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options] [FILE]\n", prog);
    fprintf(stderr, "\neezott - typed front end for eezo: checks a program and erases it to eezoc source\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  -c            Check only; emit nothing\n");
    fprintf(stderr, "  -t NAME       Print the type of the definition NAME after checking\n");
    fprintf(stderr, "  -K            Keep every transport at run time (no shortcut along constant lines)\n");
    fprintf(stderr, "  -h            Show this help\n");
    fprintf(stderr, "\nInput is read from FILE, or stdin if absent. Output is eezoc source on stdout.\n");
}

int main(int argc, char **argv) {
    int check_only = 0; const char *fname = NULL, *show = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-h")) { usage(argv[0]); return 0; }
        else if (!strcmp(argv[i], "-c")) check_only = 1;
        else if (!strcmp(argv[i], "-K")) keep_kan = 1;
        else if (!strcmp(argv[i], "-t")) { if (++i >= argc) { usage(argv[0]); return 1; } show = argv[i]; }
        else if (argv[i][0] == '-' && argv[i][1]) { fprintf(stderr, "unknown option %s\n", argv[i]); usage(argv[0]); return 1; }
        else fname = argv[i];
    }
    FILE *in = stdin;
    if (fname) { in = fopen(fname, "r"); if (!in) die("cannot open %s", fname); }
    char *src = slurp(in);
    SDecl *prog = parse_program(src, fname ? fname : "<stdin>");
    elab_program(prog);
    if (show) {
        int found = 0;
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, show)) {
            const char *names[1024]; fprintf(stderr, "%s : ", show); term_print(stderr, quote(0, defs[i].vty), names, 0); fputc('\n', stderr); found = 1;
        }
        if (!found) die("-t: no definition named '%s'", show);
    }
    if (!check_only) erase_program(stdout);
    return 0;
}
