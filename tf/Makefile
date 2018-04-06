NUM_BATCHES = 10

default: train move

setup: test_images
	python3 extract_emnist.py

all: setup batches train move

train:
	python3 train.py --dataset emnist

eval:
	python3 eval.py --dataset emnist

test_images:
	python3 make_test_images.py # make test_images.pkl.gz

batches:
	python3 make_simple_data.py $(NUM_BATCHES) # make batches

move:
	cp models/default/params.pkl.gz ../params.pkl.gz # copy model parameters
