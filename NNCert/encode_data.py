import pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np
import struct

path = sys.argv[1]

EPSILON = 0.01

# Number of bits (e.g., 16 or 32) per floating-point parameter
N = 16

def load_data(path):
    with open(path, 'rb') as f:
        return pickle.load(f, encoding='latin1')

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

# This function stolen from code posted to:
# https://stackoverflow.com/questions/16444726/binary-representation-of-float-in-python-bits-not-hex
def binary(num):
  return ''.join(bin(c).replace('0b', '').rjust(8, '0')
                 for c in struct.pack('!f', num))
# END stolen

def float_cast(f):
    if N == 32: return np.float32(f)
    elif N == 16: return np.float16(f)
    else: return f

# # MODEL output of float_to_bin:
# Definition bvec_1p0 : t := bits_to_bvec [23%N;24%N;25%N;26%N;27%N;28%N;29%N].
# # Indices record the '1' bits.
def float_to_bin(f):
    b = binary(float_cast(f).item())
    l = zip(list(range(N)), [i for i in b])
    r = map(lambda x: str(x[0]) + '%N', filter(lambda x: x[1] == '1', l))
    return '(bits_to_bvec [' + ';'.join(r) + '])'

def flatten(l): return [item for sublist in l for item in sublist]

# Network preamble
#  D = dimensionality
#  OUT = number of outputs
def the_preamble(D, OUT):
    return """
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import dyadic net bitnet out.

Import out.TheNet.
Import TheNet. Import F. Import FT. Import NETEval. Import NET.
Import DyadicFloat{}. (*for bits_to_bvec*)

Open Scope list_scope.
Notation b := bits_to_bvec.
Notation "'mk' x" := (@InputEnv.Ix.mk x _) (at level 65).
""".format(N)
    
# Declare inputs
def declare_inputs(D):
    out = ''
    for i in range(D):
        out += 'Program Definition x_{} := mk {}.\n'.format(i, i)
    return out
    
# Produce the output Coq file
def to_coq(images, labels, D, OUT):
    out = ''
    out += the_preamble(D, OUT)
    out += declare_inputs(D) + '\n'
    for i in range(len(images)):
        out += 'Definition X_' + str(i) + ':=' \
                   + images[i] + '.\n'
    out += 'Definition samples:=' + \
           '::'.join(['X_%d' % i for i in range(len(images))]) + '::nil.\n'
    out += 'Definition labels:=' + \
           '::'.join(['%d' % l for l in labels]) + '::nil.\n'
    return out

# Load the weights
train_data = load_data(path)
images = train_data.images[:100]
labels = train_data.labels[:100]

# print(len(images))
# print(len(labels))
# print(len(images[0]))
# print(labels[0])

def encode_image(image):
    s = 'InputEnv.of_list ('
    s += '::'.join(['(x_%d,%s)' % p
                  for p in filter(lambda p: p[1] != 'b []',
                                  zip(range(len(image)),
                                      [float_to_bin(x) for x in image]))])
    return s + '::nil)'

encoded_images = list(map(encode_image, images))

# Dimensionality of the input layer
D = len(images[0])

# Create coq source
src = to_coq(encoded_images, labels, D, 10)

# Write it to file
with open("data.v", "w") as f:
    f.write(src)
