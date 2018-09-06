import gzip, pickle, sys
import numpy as np

path = sys.argv[1]
n = int(sys.argv[2])

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

# Given the min and max quantization parameters, compute the
# corresponding shift and scale values.
def compute_shift_scale(min_b, max_b, num_bits):
    shift = min_b
    scale = (max_b - min_b) / (2**num_bits - 1)
    return shift, scale

# Load the weights
weights, bounds = load_weights_bounds(path)

w0 = np.transpose(weights[0])
w1 = np.transpose(weights[1])
min0 = bounds[0]
max0 = bounds[1]
min1 = bounds[2]
max1 = bounds[3]

# We convert min/max to shift/scale here to match the Coq model.
shift0, scale0 = compute_shift_scale(min0, max0, n)
shift1, scale1 = compute_shift_scale(min1, max1, n)

print("%f %f" % (shift0, scale0))
print("%f %f" % (shift1, scale1))
print_weights(w0)
print_weights(w1)
