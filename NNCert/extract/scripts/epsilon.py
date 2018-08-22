# For a given network architecture, calculate the best epsilon that
# gives a generalization with probability greater than 1 - 10e-9.

# The script is currently specialized to the following two architectures:
# 1) 2-bit quantized EMNIST, one hidden layer of size 10
# 2) 16-bit EMNIST, one hidden layer of size 10

from sympy import *

def epsilon(size_parameter_space, num_examples):
    max_eps = 1.0
    min_eps = 0.0
    eps = min_eps + (max_eps - min_eps) / 2.0
    max_iters = 100
    for i in range(0, max_iters):
        prob = N(size_parameter_space * exp(-2 * eps * eps * num_examples))
        #DEBUG: print("eps=", eps, "prob=", prob)
        if prob < 10e-9: max_eps = eps
        else: min_eps = eps
        eps = min_eps + (max_eps - min_eps)/2.0
    return eps

emnist_training_set_size=240000
emnist_test_set_size=40000

print("UNION: 2-bit quantized EMNIST, one 10-node hidden layer: eps={}".format(epsilon(N(2**(4*16 + 10*784*2 + 10*10*2)), N(emnist_training_set_size))))

print("UNION: 16-bit EMNIST, one 10-node hidden layer: eps={}".format(epsilon(N(2**(4*16 + 10*784*16 + 10*10*16)), N(emnist_training_set_size))))

#The holdout bounds are independent of model size.

print("HOLDOUT: 2-bit quantized EMNIST, one 10-node hidden layer: eps={}".format(epsilon(N(1), N(emnist_test_set_size))))

print("HOLDOUT: 16-bit quantized EMNIST, one 10-node hidden layer: eps={}".format(epsilon(N(1), N(emnist_test_set_size))))



