# NNCert

This directory contains code for training and transferring to Coq neural networks with verified generalizability bounds, building on the results in the parent directory `OUPL/MLCert`.

## Prerequisites

* Python 3 (tested with 3.5.2)
* numpy (>= 1.12.1)
* TensorFlow (tested with 1.6.0)

## Train a network

See instructions in `tf_quant/` and/or `tf` on generating parameter definition files from EMNIST models.

* `tf`: 16-bit floating-point models for EMNIST
* `tf_quant`: 2-bit quantized models for EMNIST

Use `make move` in one of the two directories above to copy a parameter definition file to `./params[-quantized].pkl.gz`.

## Transfer a model to Coq

### 16-bit 

To generate a Coq `.v` file from a parameter definition file for a 16-bit model, do: 

```
python3 compile_kernel.py params.pkl.gz
```

This results in the Coq source file `out.v` containing a Coq representation of the network, 
a prediction function, and proofs.

### 2-bit quantized

To generate a Coq `.v` file from a parameter definition file for a 2-bit model, do: 

```
python3 compile_quantized_kernel.py params-quantized.pkl.gz
```

This results in the Coq source file `qout.v` containing a Coq representation of the quantized network, 
a prediction function, and proofs.

## Build the Coq model and proofs

NOTE: Before this step, you should have transferred either a 16-bit or
a 2-bit quantized model to Coq (in files `out.v` or `qout.v`
respectively). Both files must exist, but you can run 'touch out.v'
for example to create an empty file.

* Build the parent directory `MLCert` first, by doing `make`.
* Then do `make` in this directory.

## Extract an executable OCaml model

NOTE: This step is kind of clunky. It can be streamlined.

* Edit file `empiricalloss.v` to import either `out` or `qout`, depending on whether you want to extract
  the normal 16-bit model or the 2-bit quantized model.
* Re-do `make`.

## Evaluate the error of an OCaml model

NOTE: Before doing this step, make sure you've done `make batches` in either `tf_quant/` or `tf/`.

NOTE: Like the previous step, this step is also kind of clunky. 

OCaml models extracted from the previous step live in file `extract/batch_test.ml`. After extracting 
an OCaml model (previous step), do:

* `cd extract`
* `rm batch_test.mli` (This is to avoid an extraction problem related to module interfaces.)
* `ocamlopt -o batch_test batch_test.ml`
* `cd scripts`
* `./train_err ../batch_test <log-file> ../batches/ <num-batches> <chunk-size>` where `<chunk-size>` is the number of batches you want to evaluate in parallel (this number should evenly divide `<num-batches>`, a reasonable value is `4`)
* Wait a long time...
* `python3 accuracy.py < <log-file>` to report total accuracy


There are also a couple sanity-check scripts for validating the output
of the generated Coq models. This is to ensure that the compilation
from Python models to Coq went as expected.

To compare the model's weights with the original weights learned in
python, do the following in the 'scripts' directory:

* ./validate_kernel.sh print_kernel temp ../../params-quantized.pkl.gz print_weights.py

The output will be the diff between weights printed from Coq and Python.


To check that the predictions are being correctly computed from the logit outputs, do:

* ./validate_predictions.sh print_logits temp.txt ../batches 100 ./validate_predictions.py
