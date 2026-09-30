/*
 * main.c - eezott driver.
 *
 *   eezott [-c] [-K] [FILE]   check FILE (or stdin); unless -c, write the erased eezoc source to stdout
 *   -K keeps every Kan operation at run time (no identity shortcut for constant lines): a differential test of the run-time rules
 *   -n NAME prints the normal form of the definition NAME (the checker's own evaluation)
 *   -A prints the elaborated program as a Cubical Agda module instead of erasing it (M20: the differential oracle)
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
/* the -L directories and the files loaded so far: Stacks of the memory layer (libeezo/mem.h), any number of either */
static Stack libdirs = { NULL, 0, 0, sizeof(const char *) };
static Stack loaded = { NULL, 0, 0, sizeof(char *) };
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
    char **cands = xalloc((libdirs.n + 4) * sizeof(char *)); int n = 0;
    if (from) cands[n++] = xsprintf("%s%s.tt", dir_of(from), name);
    for (size_t i = 0; i < libdirs.n; i++) cands[n++] = xsprintf("%s/%s.tt", STACK_AT(&libdirs, const char *, i), name);
    const char *env = getenv("EEZOTT_LIB"); if (env && *env) cands[n++] = xsprintf("%s/%s.tt", env, name);
    char exe[4096]; ssize_t k = readlink("/proc/self/exe", exe, sizeof exe - 1);
    if (k > 0) { exe[k] = 0; cands[n++] = xsprintf("%s../stdlib/tt/%s.tt", dir_of(exe), name); }
    for (int i = 0; i < n; i++) if (access(cands[i], F_OK) == 0) return cands[i];
    die("%s: cannot find the import '%s' (looked in the importing file's directory, -L directories, $EEZOTT_LIB, <eezott>/../stdlib/tt)", from ? from : "<stdin>", name);
    return NULL;
}
/* the files being loaded: each with the point its scan for imports has reached (a Stack of the memory layer, so an import
   chain is as deep as memory allows). A file's imports load first, in order, then its own declarations are parsed. */
typedef struct { char *src, *cur; const char *path; } LoadItem;
static Stack loading = { NULL, 0, 0, sizeof(LoadItem) };
static int load_begin(const char *path, char *src) {   /* 0: loaded already */
    for (size_t i = 0; i < loaded.n; i++) if (!strcmp(STACK_AT(&loaded, char *, i), path)) return 0;
    STACK_PUSH(&loaded, char *, xstrdup(path));
    if (!src) { src = read_path(path); if (!src) die("cannot open %s", path); }
    LoadItem it = { src, src, path }; STACK_PUSH(&loading, LoadItem, it);
    return 1;
}
static void load_run(void) {
    while (loading.n) {
        LoadItem *it = &STACK_TOP(&loading, LoadItem);
        char *line = it->cur, *import = NULL;
        while (*line && !import) {
            char *p = line; while (*p == ' ' || *p == '\t') p++;
            if (!strncmp(p, "#import ", 8)) {
                p += 8; while (*p == ' ' || *p == '\t') p++;
                char *start = p; while (*p && *p != '\n' && *p != ' ' && *p != '\t') p++;
                char *name = xalloc((size_t)(p - start) + 1); memcpy(name, start, (size_t)(p - start));
                if (*name) import = name;
            }
            while (*line && *line != '\n') line++;
            if (*line == '\n') line++;
        }
        it->cur = line;
        if (import) { const char *from = strcmp(it->path, "<stdin>") ? it->path : NULL; load_begin(resolve_import(from, import), NULL); continue; }
        LoadItem done = STACK_POP(&loading, LoadItem);
        SDecl *d = parse_program(done.src, done.path);
        *decls_tail = d;
        while (*decls_tail) decls_tail = &(*decls_tail)->next;
    }
}
static void load_file(const char *path) { if (load_begin(path, NULL)) load_run(); }
static void load_source(char *src, const char *path) { LoadItem it = { src, src, path }; STACK_PUSH(&loading, LoadItem, it); load_run(); }

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options] [FILE]\n", prog);
    fprintf(stderr, "\neezott - typed front end for eezo: checks a program and erases it to eezoc source\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  -c            Check only; emit nothing\n");
    fprintf(stderr, "  -t NAME       Print the type of the definition NAME after checking\n");
    fprintf(stderr, "  -K            Keep every transport at run time (no shortcut along constant lines)\n");
    fprintf(stderr, "  -n NAME       Print the normal form of the definition NAME after checking\n");
    fprintf(stderr, "  -A            Print the elaborated program as a Cubical Agda module (exit 3 if a construct has no Agda form)\n");
    fprintf(stderr, "  -C            Print the elaborated program as a cubicaltt module (exit 3 if a construct has no cubicaltt form)\n");
    fprintf(stderr, "  -I            The program is a stream function (eezo -i): emit main bare, not under the normal-form driver\n");
    fprintf(stderr, "  -L DIR        Also look for imports ('#import NAME' lines load NAME.tt once) in DIR\n");
    fprintf(stderr, "  -p FILE       Load FILE before the program, as an import (a prelude)\n");
    fprintf(stderr, "  -h            Show this help\n");
    fprintf(stderr, "\nInput is read from FILE, or stdin if absent. Output is eezoc source on stdout.\n");
}

int main(int argc, char **argv) {
    int check_only = 0, agda = 0, ctt = 0; const char *fname = NULL, *show = NULL, *nf = NULL;
    Stack preludes = STACK_INIT(const char *);
    mem_init("eezott", "EEZOTT_MAX_ALLOC");   /* the one memory layer (libeezo/mem.h): its failure path and budget */
    mem_on_die(resource_diagnostics);
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-h")) { usage(argv[0]); return 0; }
        else if (!strcmp(argv[i], "-c")) check_only = 1;
        else if (!strcmp(argv[i], "-K")) keep_kan = 1;
        else if (!strcmp(argv[i], "-N")) nf_main = 1;
        else if (!strcmp(argv[i], "-A")) agda = 1;
        else if (!strcmp(argv[i], "-C")) ctt = 1;
        else if (!strcmp(argv[i], "-I")) stream_main = 1;
        else if (!strcmp(argv[i], "-n")) { if (++i >= argc) { usage(argv[0]); return 1; } nf = argv[i]; }
        else if (!strcmp(argv[i], "-t")) { if (++i >= argc) { usage(argv[0]); return 1; } show = argv[i]; }
        else if (!strcmp(argv[i], "-L")) { if (++i >= argc) { usage(argv[0]); return 1; } STACK_PUSH(&libdirs, const char *, argv[i]); }
        else if (!strcmp(argv[i], "-p")) { if (++i >= argc) { usage(argv[0]); return 1; } STACK_PUSH(&preludes, const char *, argv[i]); }
        else if (argv[i][0] == '-' && argv[i][1]) { fprintf(stderr, "unknown option %s\n", argv[i]); usage(argv[0]); return 1; }
        else fname = argv[i];
    }
    for (size_t i = 0; i < preludes.n; i++) load_file(STACK_AT(&preludes, const char *, i));
    int nprelude = 0;   /* declarations (data members counted singly) the preludes contribute: the program's own start after them */
    for (SDecl *d = decls_head; d; d = d->next) nprelude += d->isdata == 2 ? d->nmembers : 1;
    if (fname) load_file(fname);
    else load_source(slurp(stdin), "<stdin>");
    elab_program(decls_head);
    if (show) {
        int found = 0;
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, show)) {
            const char *names[1024]; fprintf(stderr, "%s : ", show); term_print(stderr, quote(0, force(defs[i].vty)), names, 0); fputc('\n', stderr); found = 1;
        }
        if (!found) die("-t: no definition named '%s'", show);
    }
    if (nf) {
        int found = 0;
        for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, nf)) {
            const char *names[1024]; fprintf(stderr, "%s = ", nf); term_print(stderr, quote(0, nf_force(defs[i].vval)), names, 0); fputc('\n', stderr); found = 1;
        }
        if (!found) die("-n: no definition named '%s'", nf);
    }
    if (agda || ctt) {   /* the module is named after the file (Agda: the top-level module name is the file name) */
        char *mod = xstrdup("Main");
        if (fname) { const char *b = strrchr(fname, '/'); b = b ? b + 1 : fname; mod = xstrdup(b); char *dot = strrchr(mod, '.'); if (dot) *dot = 0; for (char *p = mod; *p; p++) if (*p == '-' || (*p == '_' && !ctt)) *p = ctt ? '_' : 'X'; }   /* cubicaltt: the module is the file's base name, _ allowed */
        if (ctt) return ctt_program(stdout, mod, nprelude, nf);   /* -C -n NAME: likewise, as cubicaltt (M20 F4) */
        return agda_program(stdout, mod, nprelude, nf);   /* -A -n NAME: the module carries NAME's normal-form check */
    }
    if (!check_only) erase_program(stdout);
    return 0;
}
