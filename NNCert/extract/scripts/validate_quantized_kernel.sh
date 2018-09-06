#!/bin/bash

# Run this script from its containing directory.

# Example:
# ./validate_quantized_kernel.sh print_kernel temp ../../params-quantized.pkl.gz 2

PROG_NAME=$1
LOG=$2
WEIGHTS=$3
NUM_BITS=$4

if [[ $# -lt 4 ]]; then
    echo "./validate_predictions.sh PROG_NAME LOG WEIGHTS NUM_BITS"
    exit
fi

rm ../$PROG_NAME.mli
ocamlopt ../$PROG_NAME.ml -o $PROG_NAME
./$PROG_NAME > ${LOG}_1
python3 print_quantized_weights.py $WEIGHTS $NUM_BITS > ${LOG}_2
diff ${LOG}_1 ${LOG}_2
