#!/bin/bash

# Set num_batches in empiricalloss.v.

python3 compile.py params.pkl.gz && time make && \
    time coqc empiricalloss.v -R . Top && cd extract && \
    rm batch_test.mli && time ocamlc batch_test.ml && time ./a.out
