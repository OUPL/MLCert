* 'make setup' to pre-extract the EMNIST data and generate
  test_images.pkl.gz file for the compile script. ONE TIME ONLY. If
  you just need to generate test_images.pkl.gz, run 'make
  test_images'.

* 'make batches' to generate batches for Coq network evaluation. Set
  the number of batches to generate by changing NUM_BATCHES in the
  make file.

* 'make train' to train the model.
* 'make eval' to evaluate the model in Python.
* 'make move' to copy the model parameters over for the compile
  script.

'make' by itself is equivalent to 'make train; make move'.

'make all' is equivalent to 'make setup; make batches; make train;
make move'.

Besides the model parameters, everything generated should be put in
the right place without need for additional moving or copying of
files.
