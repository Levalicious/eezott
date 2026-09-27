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
verdict() { echo "$1: $2${3:+ - $3}"; count[$1]=$(( ${count[$1]:-0} + 1 )); n=$((n+1)); [ "$1" = DISAGREE ] && status=1; }

for f in "$TT"/*.tt "$TT"/check/*.tt "$TT"/unerasable/*.tt; do
    [ -e "$f" ] || continue
    name=$(basename "$f" .tt); sub=$(basename "$(dirname "$f")"); [ "$sub" = tt ] && sub=; label="${sub:+$sub/}$name"
    mod=$(echo "$name" | tr '_-' 'XX')   # the module is named after the file (main.c does the same)
    ( ulimit -v ${FUZZ_ULIMIT_KB:-4000000}; timeout 120 "$EEZOTT" -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" -A "$f" > "$OUT/$mod.agda" 2> "$OUT/$mod.err" ); erc=$?
    if [ $erc -eq 3 ]; then verdict INEXPRESSIBLE "$label" "$(grep -oE 'UNSUPPORTED: [^-]*' "$OUT/$mod.agda" | head -1)"; continue; fi
    if [ $erc -ne 0 ]; then verdict DISAGREE "$label" "eezott -A failed (rc $erc): $(head -c 120 "$OUT/$mod.err" | tr '\n' ' ')"; continue; fi
    ( cd "$OUT" && ulimit -v ${FUZZ_AGDA_ULIMIT_KB:-6000000}; timeout ${FUZZ_AGDA_TIMEOUT:-300} "$AGDA" --cubical "$mod.agda" > "$mod.out" 2>&1 ); arc=$?
    if [ $arc -eq 0 ]; then verdict AGREE "$label"; continue; fi
    first=$(grep -vE '^Checking |^\s*$' "$OUT/$mod.out" | grep -vE "\.agda:[0-9]+,[0-9]+" | head -1 | cut -c1-140)
    case "$first" in
        *"declared irrelevant, so it cannot be used here"*) verdict KNOWN-DIFF "$label" "Empty-position irrelevance";;
        *"out of memory"*|*"Heap exhausted"*) verdict RESOURCE "$label" "$first";;
        "") [ $arc -eq 124 ] && verdict RESOURCE "$label" "timeout" || verdict DISAGREE "$label" "agda rc $arc";;
        *) verdict DISAGREE "$label" "$first";;
    esac
done
echo
echo "fuzz.sh: $n programs: AGREE ${count[AGREE]:-0}, INEXPRESSIBLE ${count[INEXPRESSIBLE]:-0}, KNOWN-DIFF ${count[KNOWN-DIFF]:-0}, RESOURCE ${count[RESOURCE]:-0}, DISAGREE ${count[DISAGREE]:-0} (modules in $OUT)"
exit $status
