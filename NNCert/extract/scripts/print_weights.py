import gzip, pickle, sys
import numpy as np

path = sys.argv[1]

def load_weights_bounds(path):
    with gzip.open(path, 'rb') as f:
        data = pickle.load(f, encoding='latin1')
    weights = data[:-4]
    bounds = data[-4:]
    return weights, bounds

def print_weights(weights):
    for i in range(weights.shape[0]):
        for j in range(weights.shape[1]):
            print("%d." % int(weights[i, j], 2), end=' ')
        print()


# Load the weights
weights, bounds = load_weights_bounds('models/default/params.pkl.gz')

w0 = np.transpose(weights[0])
w1 = np.transpose(weights[1])
min0 = bounds[0]
max0 = bounds[1]
min1 = bounds[2]
max1 = bounds[3]

print("%f %f" % (min0, max0))
print("%f %f" % (min1, max1))
print_weights(w0)
print_weights(w1)
