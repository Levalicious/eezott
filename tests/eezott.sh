#!/bin/bash
#
# eezott end-to-end tests: every typed program in tests/tt is checked, erased
# to eezoc source, compiled and run on the STG and JIT evaluators (and once more with every
# transport kept at run time, eezott -K); its output
# must equal an untyped oracle (Church booleans from the stdlib, which coincide
# with Scott booleans bit for bit; Scott naturals written as literals).
# Every program in tests/tt/bad must be rejected; every program in tests/tt/unerasable
# must typecheck but be refused at erasure (Kan operations without run-time meaning).
#
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
WS="${EEZO_WS:-$(cd "${SCRIPT_DIR}/../.." && pwd)}"   # the workspace: this repository and its siblings (libeezo, eezo, eezoc, eezott, stdlib)
EEZOTT="${EEZOTT:-$WS/eezott/eezott}"
LIB="${LIB:-$WS/stdlib/tt}"
# No cap is imposed here: the default is the system's own limits. EEZOTT_MAX_ALLOC exists for whoever wants one
# (export it and the checker picks it up); a resource abort is still never a judgement.
tt() { "$EEZOTT" -p "$LIB/prelude.tt" -p "$LIB/num.tt" -L "$LIB" "$@"; }   # num.tt: the equivalence Nat ~ Num in scope, the Nat's run-time representation (M19)
EEZOC="${EEZOC:-$WS/eezoc/eezoc}"
EEZO="${EEZO:-$WS/eezo/eezo}"
TT="${SCRIPT_DIR}/tt"
status=0; n=0

pass() { echo "PASS: $1"; n=$((n+1)); }
fail() { echo "FAIL: $1"; echo "  Expected: $2"; echo "  Got:      $3"; status=1; n=$((n+1)); }

scott_nat() {   # Scott numeral literal for n, in eezoc syntax
    local n=$1 s="z -> s -> z"
    while [ "$n" -gt 0 ]; do s="z -> s -> s($s)"; n=$((n-1)); done
    printf '%s' "$s"
}
chain_lit() {   # decimal -> the Nat at run time (M19): the canonical positional numeral, LOW word first, the top word bare (zero: zeroN)
    python3 -c 'import sys
n = int(sys.argv[1]); ws = []
while n: ws.append(n % (1 << 64)); n >>= 64
if not ws: print("zeroN"); sys.exit()
s = "topP(%dw)" % ws[-1]
for w in reversed(ws[:-1]): s = "consP(%dw)(%s)" % (w, s)
print("posN(%s)" % s)' "$1"
}
CHAIN_CONS='zeroN := h0 -> h1 -> h0\nposN := p -> h0 -> h1 -> h1(p)\ntopP := w -> h0 -> h1 -> h0(w)\nconsP := l -> p -> h0 -> h1 -> h1(l)(p)\n'
oracle() {      # kind value -> expected bitstring
    case "$1" in
        bool) printf '#import bool\n%s' "$2" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;
        nat)  printf "${CHAIN_CONS}"'n := %s;\nn' "$(chain_lit "$2")" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;   # a Nat is the chain (M18), the same for every program
        word) printf 'n := %sw;\nn' "$2" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;
        unary) printf 'n := %s;\nn' "$(scott_nat "$2")" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;   # the Nat with no equivalence in scope: the Scott numeral
        chain) printf "${CHAIN_CONS}"'n := %s;\nn' "$(chain_lit "$2")" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;   # a Nat is the chain (M17): the oracle is the literal's own words
        pair) printf "${CHAIN_CONS}"'pair := a -> b -> k -> k(a)(b)\nn := pair(%s)(%s);\nn\n' "$(chain_lit "${2%%,*}")" "$(chain_lit "${2#*,}")" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;   # the erasure's own pair of two chains, "A,B"
    esac
}
run_typed() {   # file mode ttflags -> bitstring (or ERROR)
    local erased; erased=$(tt $3 "$TT/$1" 2>&1) || { case "$erased" in *"resource limit"*) echo "RESOURCE_ERROR: $erased";; *) echo "TYPECHECK_ERROR: $erased";; esac; return; }
    local bcl; bcl=$(printf '%s\n' "$erased" | "$EEZOC" -f xbcl 2>&1) || { echo "EEZOC_ERROR: $bcl"; return; }
    echo "$bcl" | "$EEZO" -f xbcl $2 2>&1
}
checkN() {      # file: a program whose main is a higher inductive value; its run-time value must equal the run-time value of
                # the checker's normal form of main (eezott -N), printed through the same normalizer
    local a b; a=$(run_typed "$1" "" ""); b=$(run_typed "$1" "" "-N")
    if [ "$a" = "$b" ] && [ "${a#TYPECHECK_ERROR}" = "$a" ] && [ "${a#EEZOC_ERROR}" = "$a" ]; then pass "$1 = its normal form (eezott -N)"; else fail "$1 = its normal form (eezott -N)" "$b" "$a"; fi
}
checkUnary() {  # file value: the program with the prelude alone - no equivalence in scope - runs its Nat unary (M19)
    local want; want=$(oracle unary "$2")
    local erased; erased=$("$EEZOTT" -p "$LIB/prelude.tt" -L "$LIB" "$TT/$1" 2>&1) || { fail "$1 = unary $2 (no equivalence)" "$want" "$erased"; return; }
    local got; got=$(printf '%s\n' "$erased" | "$EEZOC" -f xbcl 2>&1 | "$EEZO" -f xbcl 2>&1)
    if [ "$got" = "$want" ]; then pass "$1 = unary $2 (no equivalence)"; else fail "$1 = unary $2 (no equivalence)" "$want" "$got"; fi
}
checkNF() {     # file name value: the checker's normal form of the definition (eezott -n), printed as a decimal literal (M15)
    local got; got=$(tt -c -n "$2" "$TT/$1" 2>&1 >/dev/null | grep "^$2 = ")
    if [ "$got" = "$2 = $3" ]; then pass "$1: $2 = $3 (eezott -n)"; else fail "$1: $2 = $3 (eezott -n)" "$2 = $3" "$got"; fi
}
check() {       # file kind value
    local want; want=$(oracle "$2" "$3")
    for mode in "" "-n"; do
        local got; got=$(run_typed "$1" "$mode" "")
        if [ "$got" = "$want" ]; then pass "$1 = $2 $3 (eezo $mode)"; else fail "$1 = $2 $3 (eezo $mode)" "$want" "$got"; fi
    done
    # every transport kept at run time: the run-time Kan rules must agree with the checker's shortcut
    local got; got=$(run_typed "$1" "" "-K")
    if [ "$got" = "$want" ]; then pass "$1 = $2 $3 (eezott -K)"; else fail "$1 = $2 $3 (eezott -K)" "$want" "$got"; fi
}

check minv_test.tt     nat 5
checkNF minv_test.tt m37 5
checkNF minv_test.tt m29 2
check not_true.tt      bool false
check and_or.tt        bool true
check id_poly.tt       bool true
check add_two_three.tt nat 5
check mul_two_three.tt nat 6
check id_transport.tt  bool false
check vec_sum.tt       nat 5
check list_length.tt   nat 3
check let_sharing.tt   nat 4
check large_elim.tt    bool true
check path_endpoint.tt bool true
check sym_refl.tt      nat 1
check comppath_nat.tt  nat 1
check funext_apply.tt  nat 3
check transp_const.tt  nat 2
check transp_pi.tt     nat 2
check hcomp_nat.tt     nat 2
check implicit_id.tt   nat 9
check implicit_lam.tt  nat 4
check implicit_cons.tt nat 3
check mutual_tree.tt   nat 4
check mutual_iit.tt    nat 3
check sq_rec.tt        nat 6
check hedberg_dec.tt   nat 2
check comp_nat.tt      nat 3
check hfill_bool.tt    bool true
check cong_sym.tt      nat 2
check transp_list.tt   nat 1
check hcomp_list.tt    nat 1
check transp_vec.tt    nat 5
check pathp_dep.tt     nat 1
check hcomp_vec_elim.tt nat 1
check transport_generic.tt nat 1
check transp_list_path.tt nat 1
check fam_rec.tt       nat 2
check transp_vec_path.tt nat 5
check sigma_basic.tt   nat 7
check sigma_eta.tt     nat 2
check transp_sigma.tt  nat 3
check hcomp_sigma.tt   nat 3
check ua_id.tt         nat 2
check ua_unglue.tt     nat 2
check glue_elem.tt     nat 4
check ua_not.tt        bool false
check ua_not_back.tt   bool true
check hcomp_u_transport.tt nat 1
check ua_not_comp.tt   bool false
check sym_u.tt         bool true
check comppath_u.tt    bool true
check list_of_types.tt nat 2
check id_u_cast.tt     bool true
check s1_elim.tt       bool true
check s1_winding.tt    bool false
check int_posneg.tt    nat 2
check qvec.tt          nat 4
check pushout.tt       nat 2
check pushout_indexed.tt nat 2
check torus_nat.tt     nat 4
check torus_s1.tt      bool false
check literal.tt       nat 42
check literal_fold.tt  nat 200
check level_id.tt      nat 3
check level_fam.tt     nat 3
check level_list.tt    nat 2
check hit_hcomp_elim.tt nat 3
check hcomp_vec_motive.tt nat 2
check glue_forall.tt   bool false

checkN nf_hit_hcomp.tt
checkN nf_mutual_hit.tt
checkN nf_pt_rec.tt
checkN nf_iit_elim.tt
checkN nf_hit_endpoint.tt
checkN nf_hit_nested.tt
checkN nf_torus_corner.tt
checkN nf_vec_hcomp.tt
checkN nf_route.tt
checkN nf_glue_comp.tt

# M15: literals are kernel values, the prelude's arithmetic is native on them
check   nat_literals.tt   nat 5
checkNF nat_literals.tt   big 515377520732011331036461129765621272702107522001
checkNF nat_literals.tt   five 5
check   nat_native_div.tt nat 14
check   nat_native_mod.tt nat 2
check   nat_native_pow.tt nat 81
check   nat_native_sub.tt nat 6
check   nat_native_lt.tt  nat 3
check   nat_native_eq.tt  nat 1
checkN  nat_native_div.tt
checkN  nat_native_mod.tt
checkN  nat_native_pow.tt
checkN  nat_native_sub.tt
checkN  nat_native_lt.tt
checkN  nat_native_eq.tt

# M16a: an irrelevant Sigma component; machine words in the theory, erased to the run-time primitives
check   irr_pair.tt      nat 3
check   word_ops.tt      word 5
check   word_fst.tt      chain 5           # a program that imports word: its Nat is the chain (M17)
check   word_mk.tt       word 5
check   word_lt.tt       bool true
check   word_divmod.tt   chain 3
check   word_wrap.tt     word 18446744073709551615
checkN  word_ops.tt
checkN  transport_comppath_u.tt   # M20 F3: hcomp in U inside compPath at run time (the value must be the checker's: true)
checkN  word_mk.tt
checkN  word_divmod.tt
checkN  word_wrap.tt
check   word_ring.tt   word 0
checkN  word_ring.tt
checkNF word_ops.tt      w5 5
check   word_fold.tt    word 18446744073709551615
checkN  word_fold.tt

# M16b, M17: the chain. With word.tt imported the Nat is the run-time chain of machine words and its arithmetic
# is word.tt's own folds (the pivot to A), so a program above a machine word runs on them; the oracle is the
# same value written as the chain literal. (The combinator interpreter, eezo -s, is two orders slower than the
# compiled evaluators and the folds are real work: the chain programs run on the compiled ones.)
check limb_add.tt    chain 340282366920938463481821351505477763072
check limb_mul.tt    chain 340282366920938463500268095579187314689
check limb_divmod.tt chain 340282366920938463463374607431768211455
check limb_pred.tt   chain 18446744073709551622
check limb_zero.tt   bool false
check nest_sigma.tt  pair "18446744073709551616,3"   # a Nat inside a value: the chain's code is the list's over the word's
check limb_minv.tt   chain 1                         # the inverse of 3 mod 2^127-1, 3 times it is 1
check limb_double.tt chain 36893488147419103232      # a fold with a successor step: read as an addition, its closed form by elim_add_l
check limb_plus7.tt  chain 129127208515966861312     # a fold with an addition step, its closed form by elim_add
# M19 (S4): a second type shaped like the naturals, its own equivalence and laws in scope, a literal through the forward map
check n2_rep.tt      chain 8
# and the Nat with no equivalence in scope stays unary
checkUnary add_two_three.tt 5
checkUnary mul_two_three.tt 6
check limb_square.tt chain 1                         # a fold with no closed form: the walk
check chain_walk.tt  chain 15                        # the walk, with the step's arithmetic on the chain
checkNF limb_minv.tt main 1
checkNF big_pow.tt   main 12157665459056928801
check big_pow.tt     chain 12157665459056928801
# a number no limb list can hold is not refused: the kernel states it as the native application itself, a
# rigid neutral (the pow guard, M17 S2); its laws (pow_add, pow_mul) prove what conversion cannot compute
out=$(tt -c -n huge "$TT/big_pow.tt" 2>&1 >/dev/null | grep "^huge = ")
case "$out" in "huge = pow 3 18446744073709551616")
    pass "big_pow.tt: an unholdable power is stated, not refused";;
  *) fail "big_pow.tt: an unholdable power is stated, not refused" "huge = pow 3 18446744073709551616" "$out";; esac
checkNF big_print.tt    big "1$(printf '%012000d' 0)"   # a literal's decimal, in full: the chunk buffer's regression test
checkNF deep_nf.tt       main 200000   # a constructor chain 200000 deep, forced, quoted and printed off the C stack

# sources nested far deeper than a C stack allows, generated here: parsed, checked, printed for Agda (-A) and cubicaltt (-C) and
# erased under a 256 KiB stack - nothing in the checker recurses on the C stack (S4), so each must go through
deep=$(mktemp -d)
python3 - "$deep" <<'PYEOF'
import sys
d = sys.argv[1]; n = 100000; main = "def main : Nat := zero\n"
open(d + "/parens.tt", "w").write("def t : U 1 := " + "(" * n + "U" + ")" * n + "\n" + main)
open(d + "/negs.tt", "w").write("def f (A : U) (a : A) (p : Path A a a) : Path A a a := \\i -> p (" + "~ " * n + "i)\n" + main)
open(d + "/meets.tt", "w").write("def f (A : U) (a : A) (p : Path A a a) : Path A a a := \\i -> p (" + "(i /\\ " * 20000 + "i" + ")" * 20000 + ")\n" + main)
open(d + "/lams.tt", "w").write("def f : " + "Nat -> " * 20000 + "Nat := \\" + " ".join("x%d" % j for j in range(20000)) + " -> x0\n" + main)
for k in range(3000): open(d + "/m%d.tt" % k, "w").write(("#import m%d\n" % (k + 1) if k < 2999 else "") + "def d%d : U 1 := U\n" % k)
open(d + "/imports.tt", "w").write("#import m0\n" + main)
PYEOF
for f in parens negs meets lams imports; do
    for flags in -c -A -C ""; do
        name="deep source $f.tt [${flags:-erase}] under a 256 KiB stack"
        out=$( (ulimit -s 256; tt $flags -L "$deep" "$deep/$f.tt") 2>&1 >/dev/null ); rc=$?
        if [ $rc -eq 0 ]; then pass "$name"; else fail "$name" "rc 0" "rc $rc: $(printf '%s' "$out" | head -1)"; fi
    done
done
# nested elaboration is linear (the value of a checked argument is built from its parts, not evaluated again): nests 20000
# deep of applications, implicit applications, pairs and a let-bound function's applications check within 2 GB and give
# their normal form (quadratic, each needed ~135 GB)
python3 - "$deep" <<'PYEOF'
import sys
d = sys.argv[1]; n = 20000
open(d + "/napp.tt", "w").write("def g (x : Nat) : Nat := x\ndef main : Nat := " + "g (" * n + "zero" + ")" * n + "\n")
open(d + "/nimp.tt", "w").write("def idd {A : U} (x : A) : A := x\ndef main : Nat := " + "idd (" * n + "zero" + ")" * n + "\n")
open(d + "/npair.tt", "w").write("def T : U := Sigma Nat (\\_ -> Nat)\ndef g (p : T) : Nat := fst p\ndef main : Nat := " + "g (" * n + "zero" + " , zero)" * n + "\n")
open(d + "/nlet.tt", "w").write("def main : Nat := let f : Nat -> Nat := \\x -> x in " + "f (" * n + "zero" + ")" * n + "\n")
PYEOF
for f in napp nimp npair nlet; do
    name="nested elaboration $f.tt 20000 deep within 2 GB"
    out=$( (ulimit -s 256 -v 2000000; tt -c -n main "$deep/$f.tt") 2>&1 ); rc=$?
    if [ $rc -eq 0 ] && printf '%s' "$out" | grep -q '^main = 0$'; then pass "$name"; else fail "$name" "main = 0" "rc $rc: $(printf '%s' "$out" | head -1)"; fi
done
rm -rf "$deep"

for f in "$TT"/bad/*.tt; do
    name=bad/$(basename "$f")
    out=$(tt -c "$f" 2>&1); rc=$?
    if [ $rc -eq 0 ]; then fail "$name rejected" "rejection" "accepted"
    elif printf '%s' "$out" | grep -q 'resource limit'; then fail "$name rejected" "rejection" "resource limit"
    else pass "$name rejected"; fi
done

# self-contained programs that must be rejected (no prelude: they use the prelude's names in ways the prelude forbids)
for f in "$TT"/badalone/*.tt; do
    name=badalone/$(basename "$f")
    if "$EEZOTT" -c < "$f" >/dev/null 2>&1; then fail "$name rejected" "rejection" "accepted"; else pass "$name rejected"; fi
done

for f in "$TT"/check/*.tt; do
    [ -e "$f" ] || continue
    name=check/$(basename "$f")
    out=$(tt -c "$f" 2>&1); rc=$?
    if printf '%s' "$out" | grep -q 'resource limit'; then fail "$name typechecks" "acceptance" "resource limit"
    elif [ $rc -ne 0 ]; then fail "$name typechecks" "acceptance" "$(printf '%s' "$out" | head -1)"
    else pass "$name typechecks"; fi
done

for f in "$TT"/unerasable/*.tt; do
    [ -e "$f" ] || continue
    name=unerasable/$(basename "$f")
    if ! tt -c "$f" >/dev/null 2>&1; then fail "$name typechecks" "acceptance" "rejection"
    elif tt "$f" >/dev/null 2>&1; then fail "$name refused at erasure" "refusal" "erased"
    else pass "$name typechecks but is refused at erasure"; fi
done


echo "$n cases"
exit $status
