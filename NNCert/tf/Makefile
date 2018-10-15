NUM_BITS = 2

default: all

all: train move

train:
	python3 train.py --dataset emnist --bits $(NUM_BITS) --max_steps 50000 --decay_step 25000 --learning_rate 0.01 --pca 1

eval: # Evaluate on training set
	python3 eval.py --dataset emnist --bits $(NUM_BITS) --set 2

move:
	cp models/default/params.pkl.gz ../params-quantized.pkl.gz # copy model parameters
