NUM_BATCHES = 2400
NUM_BITS = 16

default: train move

download:
	git clone https://github.com/bagnalla/emnist.git

setup: download
	python3 extract_emnist.py

all: setup batches train move

train:
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 80000 --decay_step 40000

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 3

batches:
	python3 make_simple_data.py $(NUM_BATCHES) False # make batches (False->train+validation sets)

move:
	cp models/default/params.pkl.gz ../params.pkl.gz # copy model parameters
