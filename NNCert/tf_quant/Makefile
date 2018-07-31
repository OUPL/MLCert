NUM_BATCHES = 2400
NUM_BITS = 8

default: train move

setup:
	python3 extract_emnist.py
	python3 make_test_images.py

all: setup batches train move

train:
	# python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 40000 --decay_step 20000 --learning_rate 0.01 --stop 0.925
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 80000 --decay_step 40000

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 3

test_images:
	python3 make_test_images.py # make test_images.pkl.gz

batches:
	python3 make_simple_data.py $(NUM_BATCHES) # make batches

move:
	cp models/default/params.pkl.gz ../params-quantized.pkl.gz # copy model parameters

