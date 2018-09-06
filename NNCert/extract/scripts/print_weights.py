import gzip, pickle, sys
import numpy as np

path = sys.argv[1]

def load_weights(path):
    with gzip.open(path, 'rb') as f:
        return pickle.load(f, encoding='latin1')

def print_weights(weights):
    for i in range(weights.shape[0]):
        for j in range(weights.shape[1]):
            print(weights[i, j], end=' ')
        print()

# Load the weights
weights = load_weights(path)

w0 = np.transpose(weights[0])
w1 = np.transpose(weights[1])

print_weights(w0)
print_weights(w1)
