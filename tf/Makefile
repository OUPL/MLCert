NUM_BATCHES = 10
NUM_BITS = 32

default: train move

setup: test_images
	python3 extract_emnist.py

all: setup batches train move

train:
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 60000 --decay_step 30000

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 2

test_images:
	python3 make_test_images.py # make test_images.pkl.gz

batches:
	python3 make_simple_data.py $(NUM_BATCHES) # make batches

move:
	cp models/default/params.pkl.gz ../params.pkl.gz # copy model parameters
