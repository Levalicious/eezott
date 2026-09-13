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
        bool) printf '#import bool\n%s' "$2" | "$EEZOC" | "$EEZO" ;;
        nat)  printf 'n := %s;\nn' "$(scott_nat "$2")" | "$EEZOC" | "$EEZO" ;;
    esac
}
run_typed() {   # file mode ttflags -> bitstring (or ERROR)
    local src; src=$(cat "$TT/prelude.tt" "$TT/$1")
    local erased; erased=$(printf '%s\n' "$src" | "$EEZOTT" $3 2>&1) || { echo "TYPECHECK_ERROR: $erased"; return; }
    local bcl; bcl=$(printf '%s\n' "$erased" | "$EEZOC" 2>&1) || { echo "EEZOC_ERROR: $bcl"; return; }
    echo "$bcl" | "$EEZO" $2 2>&1
}
checkN() {      # file: a program whose main is a higher inductive value; its run-time value must equal the run-time value of
                # the checker's normal form of main (eezott -N), printed through the same normalizer
    local a b; a=$(run_typed "$1" "" ""); b=$(run_typed "$1" "" "-N")
    if [ "$a" = "$b" ] && [ "${a#TYPECHECK_ERROR}" = "$a" ] && [ "${a#EEZOC_ERROR}" = "$a" ]; then pass "$1 = its normal form (eezott -N)"; else fail "$1 = its normal form (eezott -N)" "$b" "$a"; fi
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
checkN nf_hit_endpoint.tt
checkN nf_hit_nested.tt
checkN nf_torus_corner.tt
checkN nf_vec_hcomp.tt
checkN nf_route.tt
checkN nf_glue_comp.tt

for f in "$TT"/bad/*.tt; do
    name=bad/$(basename "$f")
    if cat "$TT/prelude.tt" "$f" | "$EEZOTT" -c >/dev/null 2>&1; then fail "$name rejected" "rejection" "accepted"; else pass "$name rejected"; fi
done

for f in "$TT"/check/*.tt; do
    [ -e "$f" ] || continue
    name=check/$(basename "$f")
    if cat "$TT/prelude.tt" "$f" | "$EEZOTT" -c >/dev/null 2>&1; then pass "$name typechecks"; else fail "$name typechecks" "acceptance" "$(cat "$TT/prelude.tt" "$f" | "$EEZOTT" -c 2>&1 | head -1)"; fi
done

for f in "$TT"/unerasable/*.tt; do
    [ -e "$f" ] || continue
    name=unerasable/$(basename "$f")
    if ! cat "$TT/prelude.tt" "$f" | "$EEZOTT" -c >/dev/null 2>&1; then fail "$name typechecks" "acceptance" "rejection"
    elif cat "$TT/prelude.tt" "$f" | "$EEZOTT" >/dev/null 2>&1; then fail "$name refused at erasure" "refusal" "erased"
    else pass "$name typechecks but is refused at erasure"; fi
done

echo "$n cases"
exit $status
