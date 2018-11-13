# For a given network architecture, calculate the best epsilon that
# gives a generalization with probability 1-1e-9.

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
        if prob < 1e-9: max_eps = eps
        else: min_eps = eps
        eps = min_eps + (max_eps - min_eps)/2.0
    return eps

# Calculate epsilon by solving the equation:
# 2^(size_parameter_space_bits) * exp(-2*\eps^2*m) = 1e-9
def epsilon2(size_parameter_space_bits, num_examples):
#    2^(size_parameter_space_bits) * exp(-2*eps*eps*num_examples) = 1e-9
#    exp(size_parameter_space_bits * log(2)) * exp(-2*eps*eps*num_examples) = 1e-9
#    log(exp(size_parameter_space_bits * log(2)) * exp(-2*eps*eps*num_examples)) = log(1e-9)
#    size_parameter_bits*log(2) + -2*eps*eps*num_examples = log(1e-9)
#    -2*eps*eps*num_examples = log(1e-9) - (size_parameter_space_bits*log(2))
#    eps = sqrt ( (log(1e-9) - size_parameter_space_bits*log(2)) / (-2*num_examples) )
    return N(sqrt( (log(1e-9) - size_parameter_space_bits*log(2)) / (-2*num_examples) ))

def epsilon_twoways(name, size_parameter_space_bits, num_examples):
    print(name + ": epsilon={}".format(epsilon(N(2**size_parameter_space_bits), N(num_examples))))
    print(name + ": epsilon2={}".format(epsilon2(size_parameter_space_bits, N(num_examples))))    

# print(epsilon_twoways("test", 0, 40000))
    
emnist_training_set_size=240000
emnist_test_set_size=40000

params_bits_2bit_784_10_10 = 4*16 + 784*10*2 + 10*10*2
params_bits_16bit_784_10_10 = 4*16 + 784*10*16 + 10*10*16

print('2-bit quantized # bits: %d' % params_bits_2bit_784_10_10)
print('16-bit float # bits: %d' % params_bits_16bit_784_10_10)

epsilon_twoways(
    "UNION: 2-bit quantized EMNIST, one 10-node hidden layer",
    params_bits_2bit_784_10_10,
    emnist_training_set_size)

epsilon_twoways(
    "UNION: 16-bit float EMNIST, one 10-node hidden layer",
    params_bits_16bit_784_10_10,
    emnist_training_set_size)

#The holdout bounds are independent of model size.

epsilon_twoways("HOLDOUT: 2-bit quantized EMNIST, one 10-node hidden layer",
                0, emnist_test_set_size)

epsilon_twoways("HOLDOUT: 16-bit quantized EMNIST, one 10-node hidden layer",
                0, emnist_test_set_size)


# A third way

from math import e
target = 10e-9

def union_eps(n, m):
    return sqrt(((n / log(e, 2)) - log(target)) / (2*m))

def holdout_eps(m):
    return sqrt(-log(target) / (2*m))

print('A third way:')
print('these should be the same: %f, %f' % (holdout_eps(emnist_test_set_size),
                                            union_eps(0, emnist_test_set_size)))

print('UNION: 2-bit quantized: %f' % union_eps(params_bits_2bit_784_10_10,
                                               emnist_training_set_size))
print('UNION: 16-bit float: %f' % union_eps(params_bits_16bit_784_10_10,
                                            emnist_training_set_size))

print('HOLDOUT: 2-bit quantized: %f' % holdout_eps(emnist_test_set_size))
print('HOLDOUT: 16-bit float: %f' % holdout_eps(emnist_test_set_size))
