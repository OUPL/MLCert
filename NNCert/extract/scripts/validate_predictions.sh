#!/bin/bash

# Run this script from its containing directory.

# Example:
# ./validate_predictions.sh print_logits temp.txt ../batches 100

PROG_NAME=$1
LOG=$2
BATCHES_DIR=$3
BATCH_SIZE=$4

if [[ $# -lt 4 ]]; then
    echo "./validate_predictions.sh PROG_NAME LOG BATCHES_DIR BATCH_SIZE"
    exit
fi

rm ../$PROG_NAME.mli
ocamlopt ../$PROG_NAME.ml -o $PROG_NAME
./$PROG_NAME < $BATCHES_DIR/batch_0 > $LOG
python3 validate_predictions.py $LOG $BATCH_SIZE
