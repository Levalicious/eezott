/*
 * main.c - eezott driver.
 *
 *   eezott [-c] [-K] [FILE]   check FILE (or stdin); unless -c, write the erased eezoc source to stdout
 *   -K keeps every Kan operation at run time (no identity shortcut for constant lines): a differential test of the run-time rules
 *   -n NAME prints the normal form of the definition NAME (the checker's own evaluation)
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

/* ---- imports (M16b): '#import NAME' loads NAME.tt once, depth-first, each file parsed on its own ---- */
#include <unistd.h>
static const char *libdirs[32]; static int nlibdirs;
static char *loaded[256]; static int nloaded;
static SDecl *decls_head, **decls_tail = &decls_head;

static char *read_path(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) return NULL;
    char *src = slurp(f); fclose(f); return src;
}
static char *dir_of(const char *path) {
    const char *slash = strrchr(path, '/');
    if (!slash) return xstrdup("./");
    char *d = xalloc((size_t)(slash - path) + 2); memcpy(d, path, (size_t)(slash - path) + 1); return d;
}
static char *resolve_import(const char *from, const char *name) {
    char *cands[40]; int n = 0;
    if (from) cands[n++] = xsprintf("%s%s.tt", dir_of(from), name);
    for (int i = 0; i < nlibdirs; i++) cands[n++] = xsprintf("%s/%s.tt", libdirs[i], name);
    const char *env = getenv("EEZOTT_LIB"); if (env && *env) cands[n++] = xsprintf("%s/%s.tt", env, name);
    char exe[4096]; ssize_t k = readlink("/proc/self/exe", exe, sizeof exe - 1);
    if (k > 0) { exe[k] = 0; cands[n++] = xsprintf("%s../stdlib/tt/%s.tt", dir_of(exe), name); }
    for (int i = 0; i < n; i++) if (access(cands[i], F_OK) == 0) return cands[i];
    die("%s: cannot find the import '%s' (looked in the importing file's directory, -L directories, $EEZOTT_LIB, <eezott>/../stdlib/tt)", from ? from : "<stdin>", name);
    return NULL;
}
static void load_source(char *src, const char *path);
static void load_file(const char *path) {
    for (int i = 0; i < nloaded; i++) if (!strcmp(loaded[i], path)) return;
    if (nloaded == 256) die("too many imported files");
    loaded[nloaded++] = xstrdup(path);
    char *src = read_path(path); if (!src) die("cannot open %s", path);
    load_source(src, path);
}
/* the file's imports first (in order), then its own declarations */
static void load_source(char *src, const char *path) {
    for (char *line = src; *line; ) {
        char *p = line; while (*p == ' ' || *p == '\t') p++;
        if (!strncmp(p, "#import ", 8)) {
            p += 8; while (*p == ' ' || *p == '\t') p++;
            char *start = p; while (*p && *p != '\n' && *p != ' ' && *p != '\t') p++;
            char *name = xalloc((size_t)(p - start) + 1); memcpy(name, start, (size_t)(p - start));
            if (*name) load_file(resolve_import(strcmp(path, "<stdin>") ? path : NULL, name));
        }
        while (*line && *line != '\n') line++;
        if (*line == '\n') line++;
    }
    SDecl *d = parse_program(src, path);
    *decls_tail = d;
    while (*decls_tail) decls_tail = &(*decls_tail)->next;
}

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options] [FILE]\n", prog);
    fprintf(stderr, "\neezott - typed front end for eezo: checks a program and erases it to eezoc source\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  -c            Check only; emit nothing\n");
    fprintf(stderr, "  -t NAME       Print the type of the definition NAME after checking\n");
    fprintf(stderr, "  -K            Keep every transport at run time (no shortcut along constant lines)\n");
    fprintf(stderr, "  -n NAME       Print the normal form of the definition NAME after checking\n");
    fprintf(stderr, "  -L DIR        Also look for imports ('#import NAME' lines load NAME.tt once) in DIR\n");
    fprintf(stderr, "  -p FILE       Load FILE before the program, as an import (a prelude)\n");
    fprintf(stderr, "  -h            Show this help\n");
    fprintf(stderr, "\nInput is read from FILE, or stdin if absent. Output is eezoc source on stdout.\n");
}

int main(int argc, char **argv) {
    int check_only = 0; const char *fname = NULL, *show = NULL, *nf = NULL;
    const char *preludes[32]; int npreludes = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-h")) { usage(argv[0]); return 0; }
        else if (!strcmp(argv[i], "-c")) check_only = 1;
        else if (!strcmp(argv[i], "-K")) keep_kan = 1;
        else if (!strcmp(argv[i], "-N")) nf_main = 1;
        else if (!strcmp(argv[i], "-n")) { if (++i >= argc) { usage(argv[0]); return 1; } nf = argv[i]; }
        else if (!strcmp(argv[i], "-t")) { if (++i >= argc) { usage(argv[0]); return 1; } show = argv[i]; }
        else if (!strcmp(argv[i], "-L")) { if (++i >= argc || nlibdirs == 32) { usage(argv[0]); return 1; } libdirs[nlibdirs++] = argv[i]; }
        else if (!strcmp(argv[i], "-p")) { if (++i >= argc || npreludes == 32) { usage(argv[0]); return 1; } preludes[npreludes++] = argv[i]; }
        else if (argv[i][0] == '-' && argv[i][1]) { fprintf(stderr, "unknown option %s\n", argv[i]); usage(argv[0]); return 1; }
        else fname = argv[i];
    }
    for (int i = 0; i < npreludes; i++) load_file(preludes[i]);
    if (fname) load_file(fname);
    else load_source(slurp(stdin), "<stdin>");
    elab_program(decls_head);
    if (show) {
        int found = 0;
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, show)) {
            const char *names[1024]; fprintf(stderr, "%s : ", show); term_print(stderr, quote(0, defs[i].vty), names, 0); fputc('\n', stderr); found = 1;
        }
        if (!found) die("-t: no definition named '%s'", show);
    }
    if (nf) {
        int found = 0;
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, nf)) {
            const char *names[1024]; fprintf(stderr, "%s = ", nf); term_print(stderr, quote(0, defs[i].vval), names, 0); fputc('\n', stderr); found = 1;
        }
        if (!found) die("-n: no definition named '%s'", nf);
    }
    if (!check_only) erase_program(stdout);
    return 0;
}
