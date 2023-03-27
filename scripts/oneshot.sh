#/bin/bash

LIB="stdlib.out"
THM=$1

SIZES=$(./crabpi $LIB count $THM)
IFS=',' read pf_size num_terms ctx_size num_lifts num_inds num_pub_terms num_rules num_nnrs num_nrs num_axioms <<< $SIZES

SED_TEMPLATE="s/__PROOF_SIZE/$pf_size/g; s/__NUM_TERMS/$num_terms/g; s/__CONTEXT_SIZE/$ctx_size/g; s/__NUM_LIFTS/$num_lifts/g; s/__NUM_INDS/$num_inds/g; s/__NUM_PUB_TERMS/$num_pub_terms/g; s/__NUM_RULES/$num_rules/g; s/__NUM_NNRS/$num_nnrs/g; s/__NUM_NRS/$num_nrs/g; s/__NUM_AXIOMS/$num_axioms/g;"

sed "$SED_TEMPLATE" zok/meta.zok.template > zok/meta.zok

./crabpi $LIB export $THM > $THM.in

time ./circ zok/eval.zok r1cs --proof-system mirage --action oneshot --inputs $THM.in
