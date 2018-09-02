#!/bin/bash

# Example:
# ./scripts/validate_kernel.sh print_kernel temp ../../params.pkl.gz print_weights.py 

PROG_NAME=$1
LOG=$2
WEIGHTS=$3
PY_SCRIPT=$4

if [[ $# -lt 4 ]]; then
    echo "./validate_predictions.sh PROG_NAME LOG WEIGHTS PY_SCRIPT"
    exit
fi

rm ../$PROG_NAME.mli
ocamlopt ../$PROG_NAME.ml -o $PROG_NAME
./$PROG_NAME > ${LOG}_1
python3 $PY_SCRIPT $WEIGHTS > ${LOG}_2
diff ${LOG}_1 ${LOG}_2
