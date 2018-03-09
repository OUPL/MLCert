import gzip, pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np
import struct

path = sys.argv[1]

EPSILON = 0.01

N = 32

def load_weights(path):
    with gzip.open(path, 'rb') as f:
        weights = pickle.load(f, encoding='latin1')
    return weights

# Load MNIST images
def load_images(path):
    with gzip.open(path, 'rb') as f:
        images = pickle.load(f, encoding='latin1')
    return images

NetTag = Enum('NetTag', 'IN RELU COMB')
class Net(object):
    def __init__(self, tag, data=None):
        self.tag = tag
        self.data = data

# This function stolen from code posted to:
# https://stackoverflow.com/questions/16444726/binary-representation-of-float-in-python-bits-not-hex
def binary(num):
  return ''.join(bin(c).replace('0b', '').rjust(8, '0')
                 for c in struct.pack('!f', num))
# END stolen

# # MODEL output of float_to_bin:
# Definition bvec_1p0 : t := bits_to_bvec [23%N;24%N;25%N;26%N;27%N;28%N;29%N].
# # Indices record the '1' bits.
def float_to_bin(f):
    b = binary(f.item())
    l = zip(list(range(N)), [i for i in b])
    # Why does python3 get rid of pattern-matching on tuples in the arguments
    # to lambdas? ARGH
    def to_N(i_v):
        i, v = i_v
        return str(i) + '%N'
    def has_onebit(i_v):
        i, v = i_v
        return v=='1'
    r = map(to_N, filter(has_onebit, l)) #just the nonzero indices
    return '(bits_to_bvec [' + ';'.join(r) + '])'

# Create the input layer
# NOTE: Need to make sure we define (using Program Definition)
# all variables in range [0, len(D))
def make_inputs(D):
    return [Net(NetTag.IN, 'x_%d' % i) for i in range(D)]

# Create a hidden layer (with relu=True) or the last layer (relu=False).
def make_layer(w, k, relu=False):
    nets = []
    for j in range(w.shape[1]):
        weights = w[:,j]
        terms = [(weights[i], 'n_%d_%d' % (k, i))
                 for i in range(weights.shape[0])]
        comb = Net(NetTag.COMB, terms)
        nets.append(Net(NetTag.RELU, comb) if relu else comb)
    return nets

def flatten(l): return [item for sublist in l for item in sublist]

# Create all layers and return a list of layers
# D is the network's input dimensionality
def make(W, D):
    input_layer = make_inputs(D)
    hidden_layers = [make_layer(W[i], i, True) for i in range(len(W)-1)]
    last_layer = make_layer(W[len(W)-1], len(W)-1, False)
    return [input_layer] + hidden_layers + [last_layer]

# Inductive t : Type :=
# | NIn : var -> t
# | NReLU : t -> t
# | NComb : list (PARAMS.t * t) -> t.

# Pretty-print a net to Coq
def net_to_coq(net):
    if net.tag == NetTag.IN:
        return 'i(' + net.data + ')'
    elif net.tag == NetTag.RELU:
        return 'r(' + net_to_coq(net.data) + ')'
    elif net.tag == NetTag.COMB:
        out = 'c('
        for i in range(len(net.data)):
            (w, id) = net.data[i]
            out += '(' + float_to_bin(w) + ',' + id + ')'
            if i < len(net.data) - 1: out += '::'
        return out + '::nil)'
    else:
        print('Error in print_to_coq: unknown net tag.')
        return None

# Network preamble
def the_preamble(D):
    return """
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import dyadic net bitnet.

Module TheDimensionality.
Definition n : nat := {}. Lemma n_gt0 : (0 < {})%nat. by []. Qed.
End TheDimensionality.
Module TheNet := NetEval TheDimensionality BitVec32Payload.
Import TheNet. Import NET.

Open Scope list_scope.
Notation "\'i\' ( x )":=(NIn x) (at level 65).
Notation "\'r\' ( x )":=(NReLU x) (at level 65).
Notation "\'c\' ( x )":=(NComb x) (at level 65).
""".format(D, D)
    
# Declare inputs
def declare_inputs(D):
    out = ''
    for i in range(D):
        out += 'Program Definition x_{} : var := @Env.Ix.mk {} _.\n'.format(i, i)
    return out
    
# Produce the output Coq file
def to_coq(layers, D):
    out = ''
    out += the_preamble(D)        
    out += declare_inputs(D)
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
W = load_weights(path)

# Filter out bias weights
W = list(filter(lambda w: len(w.shape) > 1, W))

for w in W: print(w.shape)

# Dimensionality of the input layer
D = len(images[0])

# Make all layers
layers = make(W, D)

# Create coq source
src = to_coq(layers, D)

# Write it to file
with open("out.v", "w") as f:
    f.write(src)
