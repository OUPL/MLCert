import numpy as np


def quantize(x, min_bound, max_bound, num_bits=8):
    return  "{0:b}".format(
        int(round((2**(num_bits) - 1) * \
                  (x - min_bound) / (max_bound-min_bound))))


def quantize_ndarray(a, min_bound, max_bound, num_bits=8):
    shape = a.shape
    b = []
    for x in a.flatten():
        b.append(quantize(x, min_bound, max_bound, num_bits))
    b = [w.zfill(num_bits) for w in b]
    return np.array(b).reshape(shape)


# Saving as unsigned bit vectors:
# B = [(2**bits - 1) * (a - min) / (max-min) for a in A]
# Do this then round to the nearest integer. E.g., with 2 bits, the
# weights will become 0, 1, 2, and 3.


def dequantize(x, min_bound, max_bound, num_bits=8):
    return int(x, 2) * (max_bound-min_bound) / (2**(num_bits) - 1) + min_bound


def dequantize_ndarray(a, min_bound, max_bound, num_bits=8):
    shape = a.shape
    b = []
    for x in np.squeeze(a.flatten()):
        b.append(dequantize(x, min_bound, max_bound, num_bits))
    return np.array(b).reshape(shape)
