#!/bin/bash

# Run this script from its containing directory.

# Example:
# ./validate_kernel.sh print_kernel temp ../../params.pkl.gz

PROG_NAME=$1
LOG=$2
WEIGHTS=$3

if [[ $# -lt 3 ]]; then
    echo "./validate_predictions.sh PROG_NAME LOG WEIGHTS"
    exit
fi

rm ../$PROG_NAME.mli
ocamlopt ../$PROG_NAME.ml -o $PROG_NAME
./$PROG_NAME > ${LOG}_1
python3 print_weights.py $WEIGHTS $NUM_BITS > ${LOG}_2
python3 validate_kernel.py ${LOG}_1 ${LOG}_2
