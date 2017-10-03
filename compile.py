import gzip, pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np

path = sys.argv[1]

EPSILON = 0.01

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

def float_to_D(f):
    if isinstance(f, np.float32):
        f = f.item()
    # For some reason the denominator of this fraction is always a
    # power of 2 (or very close to one) which is very convenient
    frac = Fraction(f)
    num = frac.numerator
    if abs(int(log(frac.denominator, 2)) - log(frac.denominator, 2)) \
       > 0.000000001:
        print('fraction denominator not a power of 2.')
    denom = int(log(frac.denominator, 2))
    if denom == 0:
        num *= 2
        denom += 1
    return 'd(' + str(num) + ')' + str(denom)

# Create the input layer
def make_inputs(x):
    # TODO
    return [Net(NetTag.IN,
                'lh(' + float_to_D(i-EPSILON) + ')('
                + float_to_D(i+EPSILON) + ')')
            for i in x]

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
def make(W, x):
    input_layer = make_inputs(x)
    hidden_layers = [make_layer(W[i], i, True) for i in range(len(W)-1)]
    last_layer = make_layer(W[len(W)-1], len(W)-1, False)
    return [input_layer] + hidden_layers + [last_layer]

# Inductive net {T} `{domain T} : Type :=
# | NIn : forall t : T,  net
# | NReLU : net -> net
# | NComb : list (weight * net) -> net.

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
            out += '(' + float_to_D(w) + ',' + id + ')'
            if i < len(net.data) - 1: out += '::'
        return out + '::nil)'
    else:
        print('Error in print_to_coq: unknown net tag.')
        return None
        
# Produce the output Coq file
def to_coq(layers):
    out = 'Require Import dyadic net.\n'
    out += 'Open Scope list_scope.\n'
    out += 'Notation "\'d\' ( x ) y":=(Dmake x y) (at level 60).\n'
    out += 'Notation "\'lh\' ( x ) y":=(Dlh x y) (at level 63).\n'        
    out += 'Notation "\'i\' ( x )":=(NIn x) (at level 65).\n'
    out += 'Notation "\'r\' ( x )":=(NReLU x) (at level 65).\n'
    out += 'Notation "\'c\' ( x )":=(NComb x) (at level 65).\n'
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

# Make all layers
layers = make(W, images[0])

# Create coq source
src = to_coq(layers)

# Write it to file
with open("out.v", "w") as f:
    f.write(src)
