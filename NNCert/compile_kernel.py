## NOT UPDATED FOR NEW COMPILATION SCHEME

import gzip, pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np
import struct

path = sys.argv[1]

# Number of bits (e.g., 16 or 32) per weight
N = 16

NUM_CLASSES = 10

def load_weights(path):
    with gzip.open(path, 'rb') as f:
        weights = pickle.load(f, encoding='latin1')
    return weights

# Load images
def load_images(path):
    with gzip.open(path, 'rb') as f:
        images = pickle.load(f, encoding='latin1')
    return images

NetTag = Enum('NetTag', 'IN RELU COMB')
class Net(object):
    def __init__(self, tag, data=None):
        self.tag = tag
        self.data = data

# # This function stolen from code posted to:
# # https://stackoverflow.com/questions/16444726/binary-representation-of-float-in-python-bits-not-hex
# def binary(num):
#   return ''.join(bin(c).replace('0b', '').rjust(8, '0')
#                  for c in struct.pack('!f', num))
# # END stolen

# def float_cast(f):
#     if N == 32: return np.float32(f)
#     elif N == 16: return np.float16(f)
#     else: return f

def binary(f, num_bits):
    if num_bits == 32:
        return ''.join(bin(c).replace('0b', '').rjust(8, '0')
                       for c in struct.pack('!f', np.float32(f).item()))
    elif num_bits == 16:
        return str(bin(np.float16(f).view('H'))[2:].zfill(16))
    else:
        return None

# Indices record the '1' bits.
def float_to_bin(f, num_bits):
    # b = binary(float_cast(f).item())
    # b = b[:N][::-1]
    b = binary(f, num_bits)[::-1]
    l = zip(list(range(num_bits)), [i for i in b])
    # Just the nonzero indices
    r = map(lambda p: str(p[0]) + '%N', filter(lambda x: x[1] == '1', l))
    return '(bits_to_bvec [' + ';'.join(r) + '])'

# Create the input layer
# NOTE: Need to make sure we define (using Program Definition)
# all variables in range [0, len(IN))
def make_inputs(IN):
    return [Net(NetTag.IN, 'x_%d' % i) for i in range(IN)]

# Create a hidden layer (with relu=True) or the last layer (relu=False).
def make_layer(w, k, cur_var=0, relu=False):
    nets = []
    x = cur_var
    for j in range(w.shape[1]):
        weights = w[:,j]
        terms = []
        for i in range(weights.shape[0]):
            terms += [('w_%d' % x, 'n_%d_%d' % (k, i))]
    # for j in range(w.shape[0]):
    #     weights = w[j,:]
    #     terms = []
    #     for i in range(weights.shape[0]):
    #         terms += [('w_%d' % x, 'n_%d_%d' % (k, i))]
            x += 1
        comb = Net(NetTag.COMB, terms)
        nets.append(Net(NetTag.RELU, comb) if relu else comb)
    return nets

# Create all layers and return a list of layers
# IN is the network's input dimensionality
# D is the number of parameters
def make(W, IN, D):
    input_layer = make_inputs(IN)
    cur_var = 0        
    hidden_layers = []
    for i in range(len(W) - 1):
        hidden_layers += [make_layer(W[i], i, cur_var, True)]
        x,y = W[i].shape
        cur_var += x*y
        print('hidden_layer=%d, size=%d' % (i, cur_var))
    last_layer = make_layer(W[len(W)-1], len(W)-1, cur_var, False)
    return [input_layer] + hidden_layers + [last_layer]

# Pretty-print a net to Coq
def net_to_coq(net):
    if net.tag == NetTag.IN:
        return 'i(' + net.data + ')'
    elif net.tag == NetTag.RELU:
        return 'r(' + net_to_coq(net.data) + ')'
    elif net.tag == NetTag.COMB:
        out = 'c('
        for i in range(len(net.data)):
            (w_id, id) = net.data[i]
            out += '(' + w_id + ',' + id + ')'
            if i < len(net.data) - 1: out += '::'
        return out + '::nil)'
    else:
        print('Error in print_to_coq: unknown net tag.')
        return None

# Network preamble
#  IN = dimensionality of the input space
#  NEURONS = number of neurons in the hidden layer
#  OUT = number of outputs
def the_preamble(IN, NEURONS, OUT):
    return """Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic OUVerT.compile net bitnet kernel.

Module TheDimensionality. Definition n : nat := N.to_nat {}. 
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End TheDimensionality.
Module Neurons. Definition n : nat := N.to_nat {}.
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End Neurons.
Module Outputs. Definition n : nat := {}. Lemma n_gt0 : (0 < {})%nat. by []. Qed. End Outputs.
Import DyadicFloat16.
Module K := Kernel TheDimensionality Neurons Outputs BitVecPayload BitVecPayload.
Module B16PayloadMap <: PayloadMap BitVecPayload.
  Definition f := to_dyadic.
End B16PayloadMap.
Module KTranslate := KernelTranslate TheDimensionality Neurons
                                     Outputs BitVecPayload BitVecPayload
                                     B16PayloadMap B16PayloadMap K.
Import KTranslate. Import TheNet.
Import F. Import NETEval. Import NET.

Open Scope list_scope.
Notation "\'i\' ( x )":=(NIn x) (at level 65).
Notation "\'r\' ( x )":=(NReLU x) (at level 65).
Notation "\'c\' ( x )":=(NComb x) (at level 65).
""".format(IN, IN, NEURONS, NEURONS, OUT, OUT)

def translate_code():
    return 'Definition theta := translate kernel.\n'
    
# Declare input and weight variables
def declare_inputs(IN):
    out = ''
    for i in range(IN):
        out += 'Program Definition x_{} : input_var := @InputEnv.Ix.mk {} _.\n'.format(i, i)
    return out

def declare_weights(D):
    out = ''
    for i in range(D):
        out += 'Program Definition w_{} : param_var := @ParamEnv.Ix.mk {} _.\n'.format(i, i)
    return out

# bits_to_bvec [0%N;3%N;4%N;5%N;6%N;9%N;11%N;13%N;15%N]

def to_bit_vector(x, num_bits):
    # return 'bits_to_bvec [' + ';'.join([a + '%N' for a in x]) + ']'
    # print(x)
    l = zip(list(range(num_bits)), [i for i in x])
    r = map(lambda p: str(p[0]) + '%N', filter(lambda x: x[1] == '1', l))
    return '(bits_to_bvec [' + ';'.join(r) + '])'


# Definition theta : ParamEnv.t :=
#   ParamEnv.of_fun (fun i => match i with
#                             | ParamEnv.Ix.mk i' _ => if N.eqb i' 0 then Dpos 1 else Dneg 1
#                             end).


# Build a vector using of_fun.
# X - list of elements (strings)
# namespace - the Vector module to use
# default - default element (string)
def build_vector(X, namespace, default):
    out = '(%s.of_fun (fun ix => match ix with %s.Ix.mk ix\' _ =>\n' \
          % (namespace, namespace)
    i = 0
    for x in X:
        out += 'if N.eqb ix\' %d then %s else\n' % (i, x)
        i += 1
    out += '%s end))' % default
    return out

    
def build_kernel(shift0, scale0, shift1, scale1, w0, w1):
    return 'K.Build_t (%s, %s) (%s, %s) %s %s' \
        % (shift0, scale0, shift1, scale1, w0, w1)

# Produce the output Coq file
def to_coq(IN, NEURONS, OUT, kernel, layers):
    out = ''
    out += the_preamble(IN, NEURONS, OUT)
    out += '\nDefinition kernel := ' + kernel + '.\n'
    out += translate_code()
    out += declare_inputs(IN) + '\n'
    out += declare_weights(IN*NEURONS + NEURONS*OUT) + '\n'
    for i in range(len(layers)):
        layer = layers[i]
        for j in range(len(layer)):
            net = layer[j]
            out += 'Definition n_' + str(i) + '_' + str(j) + ':=' \
                   + net_to_coq(net) + '.\n'
    out += 'Definition outputs:=' + \
           ''.join(['n_' + str(len(layers)-1) + '_' + str(i) + '::'
            for i in range(len(layers[-1]))]) + 'nil.\n'
    return out

images = load_images('test_images.pkl.gz')

# Load the weights
weights = load_weights(path)

w0 = weights[0]
w1 = weights[1]

# print('w0: ' + str(w0))
# print('w1: ' + str(w1))

shift0_bits = float_to_bin(np.float16(0.0), N)
scale0_bits = float_to_bin(np.float16(1.0), N)
shift1_bits = float_to_bin(np.float16(0.0), N)
scale1_bits = float_to_bin(np.float16(1.0), N)

print(w0.shape)
print(w1.shape)

w0_bits = []
for i in range(w0.shape[1]):
    bvecs = [float_to_bin(np.float16(x), N) for x in w0[:,i]]
    vec = build_vector(bvecs, 'K.Layer1Payload.Vec', '(bits_to_bvec [])')
    w0_bits.append(vec)
print(np.array(w0_bits).shape)
w0_vec = build_vector(w0_bits, 'K.Layer1', '(K.Layer1Payload.Vec.of_list [])')

w1_bits = []
for i in range(w1.shape[1]):
    bvecs = [float_to_bin(np.float16(x), N) for x in w1[:,i]]
    vec = build_vector(bvecs, 'K.Layer2Payload.Vec', '(bits_to_bvec [])')
    w1_bits.append(vec)
print(np.array(w1_bits).shape)
w1_vec = build_vector(w1_bits, 'K.Layer2', '(K.Layer2Payload.Vec.of_list [])')

kernel = build_kernel(shift0_bits, scale0_bits, shift1_bits,
                      scale1_bits, w0_vec, w1_vec)

# Number of params
D = 0
for w in weights:
    x,y = w.shape
    D += x*y
print("total_size={}".format(D))

# Dimensionality of the input layer
IN = len(images[0])

num_neurons = w1.shape[0]

# Make all layers
layers = make(weights, IN, D)

src = to_coq(IN, num_neurons, NUM_CLASSES, kernel, layers)

# Write it to file
with open("out.v", "w") as f:
    f.write(src)
