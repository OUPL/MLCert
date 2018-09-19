NUM_BITS = 16

default: all

all: train move

train:
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 80000 --decay_step 40000

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 3

move:
	cp models/default/params.pkl.gz ../params-float.pkl.gz # copy model parameters
