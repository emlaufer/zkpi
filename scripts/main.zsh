#!/usr/bin/env zsh
trap "exit" INT TERM
trap "kill 0" EXIT

set -xe
if [ ! -f hosts ]; then
  #./analysis/collect/create_vms.zsh 48 1 n2-highmem
  ./create_vms.zsh 32 8 e2-highmem
fi
#log2sizes=(1 2 3 4 5 6)
#log2sizes=(20)
#proofs=(groth16)
#proofs=(plonk)
#trials=1

cat benches

./analysis/lib/runner.py hosts benches --output ./analysis/data/weak_1_20.csv

./analysis/collect/delete_vms.zsh
trap - INT TERM EXIT
