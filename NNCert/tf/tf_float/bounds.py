from math import *

# Compute Chernoff-style generalization bounds:
#   ln_size_h = ln(size_hypothesis_class)
#   m = number of training samples
#   delta = confidence
def bounds(ln_size_h, m, delta=0.01):
    return \
        sqrt(   (log(2) + ln_size_h + log(1 / delta)) / (2.0*m)   )

def ln_size_h(inputs=784, outputs=10, hidden_nodes=7, bitwidth=2):
    d = inputs*hidden_nodes + hidden_nodes*outputs
    return bitwidth*d / log(2, e)

def values():
    for m in range(50000, 1000000, 50000):
        print('m=%d, error_bound=%f' % (m, bounds(ln_size_h(), m)))

values()
