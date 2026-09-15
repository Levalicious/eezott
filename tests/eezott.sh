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
EEZOTT="${SCRIPT_DIR}/../eezott/eezott"
LIB="${SCRIPT_DIR}/../stdlib/tt"
# No cap is imposed here: the default is the system's own limits. EEZOTT_MAX_ALLOC exists for whoever wants one
# (export it and the checker picks it up); a resource abort is still never a judgement.
tt() { "$EEZOTT" -p "$LIB/prelude.tt" -L "$LIB" "$@"; }
EEZOC="${SCRIPT_DIR}/../eezoc/eezoc"
EEZO="${SCRIPT_DIR}/../eezo/eezo"
TT="${SCRIPT_DIR}/tt"
status=0; n=0

pass() { echo "PASS: $1"; n=$((n+1)); }
fail() { echo "FAIL: $1"; echo "  Expected: $2"; echo "  Got:      $3"; status=1; n=$((n+1)); }

scott_nat() {   # Scott numeral literal for n, in eezoc syntax
    local n=$1 s="z -> s -> z"
    while [ "$n" -gt 0 ]; do s="z -> s -> s($s)"; n=$((n-1)); done
    printf '%s' "$s"
}
oracle() {      # kind value -> expected bitstring
    case "$1" in
        bool) printf '#import bool\n%s' "$2" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;
        nat)  printf 'n := %s;\nn' "$(scott_nat "$2")" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;
        word) printf 'n := %sw;\nn' "$2" | "$EEZOC" -f xbcl | "$EEZO" -f xbcl ;;
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
check   word_fst.tt      nat 5
check   word_mk.tt       word 5
check   word_lt.tt       bool true
check   word_divmod.tt   nat 3
check   word_wrap.tt     word 18446744073709551615
checkN  word_ops.tt
checkN  word_mk.tt
checkN  word_divmod.tt
checkN  word_wrap.tt
check   word_ring.tt   word 0
checkN  word_ring.tt
check   bignat_fold.tt  nat 123
checkN  bignat_fold.tt
check   bignat_mul.tt   nat 42
checkN  bignat_mul.tt
checkNF bignat_mul.tt   main 42
checkNF word_ops.tt      w5 5
check   word_fold.tt    word 18446744073709551615

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
