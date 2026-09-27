#!/bin/bash
#
# tests/fuzz.sh - the differential test of eezott against an independent implementation (M20, stage F1).
#
# Every typed program of the suite (tests/tt, check/, unerasable/) is printed as a Cubical Agda module by the
# checker itself (eezott -A: the elaborated core, the very judgement the kernel made) and re-checked by agda's
# --cubical mode, whose primitives are eezott's. The two verdicts must agree. Per program:
#   AGREE          agda accepts what eezott accepted
#   INEXPRESSIBLE  eezott -A exits 3: the program uses a construct Agda has no form for (a path constructor whose
#                  boundary is not a full cube, a literal of a second Peano type); printed with an UNSUPPORTED comment
#   KNOWN-DIFF     agda rejects for a recorded difference between the theories (a proof of Empty is an irrelevant
#                  position in eezott, elab.c; Agda allows only the absurd pattern on an irrelevant argument)
#   RESOURCE       agda ran out of memory or time (natives compute in unary there): not a judgement
#   ORACLE-PANIC   agda hit an internal error (a bug of the oracle's): not a judgement either; reported upstream when minimised
# The run-time leg (F2): for a program whose main is a Nat or a Bool, the program is rerun as a stream function
# (main := \_ -> showNat main, stdlib/tt/show.tt: a typed Lazy-K wrapper) through eezoc's pristine ELF (-e -i) and the
# bytes it prints must be the checker's normal form of main - which the Agda module above has already judged:
#   RUN-AGREE / RUN-DISAGREE   the ELF's output against eezott -n main (zero-padded decimal, or t/f)
#   DISAGREE       everything else: a disagreement, kept under tests/fuzz/found/ once minimised, never deleted
# The oracle is consumed as installed (its exit status and text); it is never modified.
#
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
EEZOTT="${SCRIPT_DIR}/../eezott/eezott"
LIB="${SCRIPT_DIR}/../stdlib/tt"
TT="${SCRIPT_DIR}/tt"
OUT="${FUZZ_OUT:-$(mktemp -d)}"
AGDA="${AGDA:-agda}"
command -v "$AGDA" >/dev/null || { echo "fuzz.sh: agda not found (apt install agda; 2.6.4.3 suffices: only the builtin modules are used)"; exit 2; }
tt() { "$EEZOTT" -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" "$@"; }
status=0; n=0
declare -A count
verdict() { echo "$1: $2${3:+ - $3}"; count[$1]=$(( ${count[$1]:-0} + 1 )); if [ "$1" != RUN-AGREE ] && [ "$1" != RUN-DISAGREE ]; then n=$((n+1)); fi; if [ "$1" = DISAGREE ] || [ "$1" = RUN-DISAGREE ]; then status=1; fi; return 0; }

EEZOC="${SCRIPT_DIR}/../eezoc/eezoc"
runleg() {   # file label: the run-time leg for a Nat- or Bool-valued main
    local f="$1" label="$2" mty nf want show width
    case "$label" in unerasable/*) return 0;; esac   # refused at erasure by design (the gate checks that): no run-time value to observe
    mty=$("$EEZOTT" -c -t main -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" "$f" 2>&1 | sed -n 's/^main : //p' | head -1)
    case "$mty" in Nat) show=showNat; width=64;; Bool) show=showBool; width=1;; *) return 0;; esac
    nf=$("$EEZOTT" -c -n main -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" "$f" 2>&1 | sed -n 's/^main = //p' | head -1)
    case "$mty" in
        Nat) [[ "$nf" =~ ^[0-9]+$ ]] || return 0; want=$(printf '%*s' $width "$nf" | tr ' ' 0);;
        Bool) case "$nf" in true) want=t;; false) want=f;; *) return 0;; esac;;
    esac
    local w="$OUT/$(basename "$f" .tt).run.tt"
    sed -E 's/\bmain\b/mainv0/g' "$f" > "$w"; printf '\ndef main : Unit -> Out %d := \\_ -> %s mainv0\n' $width $show >> "$w"
    ( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout 120 "$EEZOTT" -I -p "$LIB/prelude.tt" -p "$LIB/num.tt" -p "$LIB/show.tt" -L "$LIB" "$w" > "$w.eezo" 2> "$w.err" ) || { verdict RUN-DISAGREE "$label" "eezott -I: $(head -c 100 "$w.err" | tr '\n' ' ')"; return 0; }
    ( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout 120 "$EEZOC" -e -i -f xbcl < "$w.eezo" > "$w.elf" 2> "$w.cerr" ) || { verdict RUN-DISAGREE "$label" "eezoc: $(head -c 100 "$w.cerr" | tr '\n' ' ')"; return 0; }
    chmod +x "$w.elf"
    local got; got=$( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout ${FUZZ_RUN_TIMEOUT:-120} "$w.elf" < /dev/null 2> "$w.rerr" ); local rc=$?
    if [ "$got" = "$want" ] && [ $rc -eq 0 ]; then verdict RUN-AGREE "$label"; else verdict RUN-DISAGREE "$label" "wanted $want, got '$got' (rc $rc) $(head -c 80 "$w.rerr" | tr '\n' ' ')"; fi
}
for f in "$TT"/*.tt "$TT"/check/*.tt "$TT"/unerasable/*.tt; do
    [ -e "$f" ] || continue
    name=$(basename "$f" .tt); sub=$(basename "$(dirname "$f")"); [ "$sub" = tt ] && sub=; label="${sub:+$sub/}$name"
    mod=$(echo "$name" | tr '_-' 'XX')   # the module is named after the file (main.c does the same)
    # the module carries main's normal form for Agda to judge when the checker can hold it (the literal-elimination
    # tripwire, exit 70, or a stack overflow on an astronomically large normal form: then the module goes without)
    nfnote=
    ( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout 120 "$EEZOTT" -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" -A -n main "$f" > "$OUT/$mod.agda" 2> "$OUT/$mod.err" ); erc=$?
    if [ $erc -ne 0 ] && [ $erc -ne 3 ]; then
        case $erc in 70|124|139) nfnote=" (main's normal form unholdable, rc $erc: module without it)";; esac   # rc 1: no main, nothing to note
        ( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout 120 "$EEZOTT" -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" -A "$f" > "$OUT/$mod.agda" 2> "$OUT/$mod.err" ); erc=$?
    fi
    if [ $erc -eq 3 ]; then verdict INEXPRESSIBLE "$label" "$(grep -oE 'UNSUPPORTED: [^-]*' "$OUT/$mod.agda" | head -1)"; runleg "$f" "$label"; continue; fi
    if [ $erc -ne 0 ]; then verdict DISAGREE "$label" "eezott -A failed (rc $erc): $(head -c 120 "$OUT/$mod.err" | tr '\n' ' ')"; continue; fi
    ( cd "$OUT" && ulimit -v ${FUZZ_AGDA_ULIMIT_KB:-6000000}; timeout ${FUZZ_AGDA_TIMEOUT:-300} "$AGDA" --cubical "$mod.agda" > "$mod.out" 2>&1 ); arc=$?
    runleg "$f" "$label"   # the run-time leg's reference is the checker's normal form, whatever Agda says of the module
    if [ $arc -eq 0 ]; then verdict AGREE "$label" "${nfnote# }"; continue; fi
    first=$(grep -vE '^Checking |^\s*$' "$OUT/$mod.out" | grep -vE "\.agda:[0-9]+,[0-9]+" | head -1 | cut -c1-140)
    case "$first" in
        *"declared irrelevant, so it cannot be used here"*) verdict KNOWN-DIFF "$label" "Empty-position irrelevance";;
        *"out of memory"*|*"Heap exhausted"*) verdict RESOURCE "$label" "$first";;
        *"Panic:"*|*"An internal error has occurred"*) verdict ORACLE-PANIC "$label" "$first";;   # the oracle itself failed: no judgement on either side
        "") if [ $arc -eq 124 ]; then verdict RESOURCE "$label" "timeout"; else verdict DISAGREE "$label" "agda rc $arc"; fi;;
        *) verdict DISAGREE "$label" "$first";;
    esac
done
echo
echo "fuzz.sh: $n programs: AGREE ${count[AGREE]:-0}, INEXPRESSIBLE ${count[INEXPRESSIBLE]:-0}, KNOWN-DIFF ${count[KNOWN-DIFF]:-0}, RESOURCE ${count[RESOURCE]:-0}, ORACLE-PANIC ${count[ORACLE-PANIC]:-0}, DISAGREE ${count[DISAGREE]:-0}; run-time leg: RUN-AGREE ${count[RUN-AGREE]:-0}, RUN-DISAGREE ${count[RUN-DISAGREE]:-0} (modules in $OUT)"
exit $status
