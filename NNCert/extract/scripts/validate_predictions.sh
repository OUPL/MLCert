#!/bin/bash

# Example:
# ./validate.sh print_logits temp.txt ../batches 100 ./validate_predictions.py

PROG_NAME=$1
LOG=$2
BATCHES_DIR=$3
BATCH_SIZE=$4
PY_SCRIPT=$5

if [[ $# -lt 5 ]]; then
    echo "./validate_predictions.sh PROG_NAME LOG BATCHES_DIR BATCH_SIZE PY_SCRIPT"
    exit
fi

rm ../$PROG_NAME.mli
ocamlopt ../$PROG_NAME.ml -o $PROG_NAME
./$PROG_NAME < $BATCHES_DIR/batch_0 > $LOG
python3 $PY_SCRIPT $LOG $BATCH_SIZE
