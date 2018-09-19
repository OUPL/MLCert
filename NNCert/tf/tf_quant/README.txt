

* 'make setup' to download and extract the EMNIST data. ONE TIME
  ONLY. Extraction may take a while.

* 'make batches' to generate batches for Coq network evaluation. Set
  the number of batches to generate by changing NUM_BATCHES in the
  makefile.

* 'make train' to train a model.
* 'make eval' to evaluate the trained model in Python.
* 'make move' to copy the model parameters up to be compiled to a Coq
  network kernel.

'make' by itself is equivalent to 'make train; make move'.

'make all' is equivalent to 'make setup; make batches; make train;
make move'.

Besides the model parameters, everything generated should be put in
the right place without need for additional moving or copying of
files.
