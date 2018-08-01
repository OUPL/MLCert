## PARTIALLY UPDATED FOR NEW COMPILATION SCHEME
## NOTE: The code below currently works only for N = 16 (TODO: N = 32)

import gzip, pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np
import struct

path = sys.argv[1]

# Number of bits (e.g., 16 or 32) per weight
# NOTE: The code below currently works only for N=16
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

# float->binary big-endian
def binary(f, num_bits):
    if num_bits == 32:
        return ''.join(bin(c).replace('0b', '').rjust(8, '0')
                       for c in struct.pack('!f', np.float32(f).item()))
    elif num_bits == 16:
        return str(bin(np.float16(f).view('H'))[2:].zfill(16))
    else:
        return None

def coqbool_of_bitchar(i):
    if i == '1': return 'T'
    elif i == '0': return 'F'
    else: raise BaseException('Nonbinary input in bool_of_bit')

def build_vector(sep, l):
    return '(V([' + sep.join(l) + ']))'
    
# Kernel expects float bitlists to be little-endian
def float_to_bin(f, num_bits):
    b = binary(f, num_bits)[::-1]
    return build_vector(';', [coqbool_of_bitchar(i) for i in b])

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
Require Import OUVerT.dyadic OUVerT.compile. 
Require Import MLCert.axioms MLCert.bitvectors MLCert.extraction_ocaml MLCert.oracleclassifiers. 
Require Import net bitnet kernel.

Module TheDimensionality. Definition n : nat := N.to_nat {}. 
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End TheDimensionality.
Module Neurons. Definition n : nat := N.to_nat {}.
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End Neurons.
Module Outputs. Definition n : nat := {}. Lemma n_gt0 : (0 < {})%nat. by []. Qed. End Outputs.
Import DyadicFloat16.

(*The following function is used only to map 16-bit FP numbers to dyadics 
  (following the IEEE 754 convention -- see bitnet.v for more details.)*)
Definition bitvec_to_bvec (n:nat) (v:bitvec n) : BitVec.t :=
  bits_to_bvec (bitvec_to_sparse_list v).

Module bitvec16Type <: TYPE.
  Definition t := bitvec 16.
End bitvec16Type.

Module bitvec16FinType <: FINTYPE.
  Definition t := bitvec_finType 16.
  Lemma card : #|t| = 2^16. Proof. by rewrite bitvec_card. Qed.
End bitvec16FinType.

Module bitvec16PayloadMap : PayloadMap bitvec16Type.
  Definition f (v:bitvec16Type.t) : DRed.t := to_dyadic (bitvec_to_bvec _ v).
End bitvec16PayloadMap.

Module K := Kernel TheDimensionality Neurons Outputs bitvec16Type bitvec16Type.

Module KFin := KernelFin TheDimensionality Neurons Outputs bitvec16FinType bitvec16FinType.

Module KTranslate := Translate TheDimensionality Neurons Outputs 
                               bitvec16Type bitvec16Type
                               bitvec16PayloadMap bitvec16PayloadMap K.
Import KTranslate. Import TheNet.
Import F. Import NETEval. Import NET.


Definition X := AxVec TheDimensionality.n (bitvec 16).
Definition Y := 'I_Outputs.n.
Definition Hypers := unit.
Definition Params := K.t.

Definition InputEnv_of_X (img:X) : NETEval.InputEnv.t :=
  KTranslate.TheNet.F.NETEval.NET.InputEnv.of_list
    (List.map (fun x_bits =>
                 let: (x,bits) := x_bits in 
                 (x, bitvec16PayloadMap.f bits))
              (zip InputEnv.Ix.enumerate_t (AxVec_to_list img))).

Definition Y_of_OutputIx (ix:Output.Ix.t) : Y := Output.Ix.Ordinal_of_t ix.

Definition predict (h:Hypers) (p:Params) (img:X) : Y :=
  let: outs := TheNet.F.seval
                 (translate_kernel p)
                 (TheNet.F.Forest.of_list
                    (combine (Forest.Ix.enumerate_t) (rev outputs)))
                 (InputEnv_of_X img)
  in Y_of_OutputIx (Output.argmax Dlt_bool outs).

Open Scope list_scope.
Notation "\'i\' ( x )":=(NIn x) (at level 65).
Notation "\'r\' ( x )":=(NReLU x) (at level 65).
Notation "\'c\' ( x )":=(NComb x) (at level 65).
Notation "\'V\' ( x )":=(@AxVec_of_list _ _ x) (at level 65).
Notation "\'T\'":=(true) (at level 65).
Notation "\'F\'":=(false) (at level 65).
""".format(IN, IN, NEURONS, NEURONS, OUT, OUT)

def the_postamble():
    return """
Definition tf_learner
  : learners.Learner.t X Y Hypers Params
  := OracleLearner kernel predict.
"""

def translate_code():
    return 'Definition theta := translate_kernel kernel.\n'
    
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
    
def build_kernel(shift0, scale0, shift1, scale1, w0, w1):
    return 'K.Build_t (%s, %s) (%s, %s) %s %s' \
        % (shift0, scale0, shift1, scale1, w0, w1)

# Produce the output Coq file
def to_coq(IN, NEURONS, OUT, kernel, layers):
    out = ''
    out += the_preamble(IN, NEURONS, OUT)
    out += '\nDefinition kernel := ' + kernel + '.\n'
    out += translate_code()
    out += the_postamble()
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
    vec = build_vector(';\n', bvecs)
    w0_bits.append(vec)
print(np.array(w0_bits).shape)
w0_vec = build_vector(';\n', w0_bits)

w1_bits = []
for i in range(w1.shape[1]):
    bvecs = [float_to_bin(np.float16(x), N) for x in w1[:,i]]
    vec = build_vector(';\n', bvecs)
    w1_bits.append(vec)
print(np.array(w1_bits).shape)
w1_vec = build_vector(';\n', w1_bits)

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
