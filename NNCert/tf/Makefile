NUM_BATCHES=2400

default: setup

setup: download extract

download:
	git clone https://github.com/bagnalla/emnist.git

extract:
	python3 extract_emnist.py

batches:
	# make batches (False->train+validation sets)
	python3 make_simple_data.py $(NUM_BATCHES) False
