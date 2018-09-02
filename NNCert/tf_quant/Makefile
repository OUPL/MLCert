NUM_BATCHES=2400
# NUM_BATCHES=2000
NUM_BITS = 2

default: train move

download:
	git clone https://github.com/bagnalla/emnist.git

setup: download
	python3 extract_emnist.py

all: setup batches train move

train:
	# python3 train.py --dataset emnist_reduced --bits $(NUM_BITS) --max_steps 50000 --decay_step 25000 --learning_rate 0.01 --stop 0.925
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 50000 --decay_step 25000 --learning_rate 0.01

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 2

batches:
	python3 make_simple_data.py $(NUM_BATCHES) # make batches

move:
	cp models/default/params.pkl.gz ../params-quantized.pkl.gz # copy model parameters

