import gzip, pickle, sys
from enum import Enum
from fractions import Fraction
from math import log
import numpy as np
import struct

path = sys.argv[1]

# Number of bits (e.g., 16 or 32) per weight
# NOTE: code below currently works only for N_W = 2
N_W = 2

# Number of bits for shift and scale values
# NOTE: code below currently works only for N_SS = 16
N_SS = 16

NUM_CLASSES = 10

def load_weights_bounds(path):
    with gzip.open(path, 'rb') as f:
        data = pickle.load(f, encoding='latin1')
    weights = data[:-4]
    bounds = data[-4:]
    return weights, bounds

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

# Network preamble
#  IN = dimensionality of the input space
#  NEURONS = number of neurons in the hidden layer
#  OUT = number of outputs
def the_preamble(IN, NEURONS, OUT):
    return """Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import Coq.Program.Basics.
Require Import OUVerT.dyadic OUVerT.compile. 
Require Import MLCert.axioms MLCert.bitvectors MLCert.learners MLCert.extraction_ocaml.
Require Import net bitnet kernel print.

Module TheDimensionality. Definition n : nat := N.to_nat {}. 
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End TheDimensionality.
Module Neurons. Definition n : nat := N.to_nat {}.
Lemma n_gt0 : (0 < N.to_nat {})%nat. by []. Qed. End Neurons.
Module Outputs. Definition n : nat := {}. Lemma n_gt0 : (0 < {})%nat. by []. Qed. End Outputs.
Module BLow <: BOUND. Definition n := {}. Lemma n_gt0 : 0 < n. Proof. by []. Qed. End BLow.
Module BLowType : TYPE. Definition t := bitvec BLow.n. End BLowType.
Import DyadicFloat16.

(*The following function is used only to map 16-bit FP numbers to dyadics 
  (following the IEEE 754 convention -- see bitnet.v for more details.)*)
Definition bitvec_to_bvec (n:nat) (v:bitvec n) : BitVec.t :=
  bits_to_bvec (bitvec_to_sparse_list v).

Module bitvec2Type <: TYPE.
  Definition t := bitvec 2.
End bitvec2Type.

Module bitvec2FinType.
  Definition t := bitvec_finType 2.
  Lemma card : #|t| = 2^2. Proof. by rewrite bitvec_card. Qed.
End bitvec2FinType.

(*In quantized networks, bitstring weights are interpreted as little-endian 
  positive binary numbers.*)
Module bitvec2PayloadMap : PayloadMap bitvec2Type.
  Definition D2 := dyadic.Dadd D1 D1.
  Definition bit_to_D (b:bool) := if b then D1 else D0.
  Definition bits_to_D bs :=
    fst (fold_left (fun (acc : D*D) b =>
                       let (sum, exp) := acc in
                       (dyadic.Dadd sum (dyadic.Dmult (bit_to_D b) exp),
                        dyadic.Dmult exp D2))
                   bs (D0, D1)).
  Definition f (v:bitvec2Type.t) : DRed.t := 
    DRed.build (bits_to_D (bitvec_to_list v)).
End bitvec2PayloadMap.

Module bitvec16Type <: TYPE.
  Definition t := bitvec 16.
End bitvec16Type.

Module bitvec16FinType.
  Definition t := bitvec_finType 16.
  Lemma card : #|t| = 2^16. Proof. by rewrite bitvec_card. Qed.
End bitvec16FinType.

Module bitvec16PayloadMap : PayloadMap bitvec16Type.
  Definition f (v:bitvec16Type.t) : DRed.t := to_dyadic (bitvec_to_bvec _ v).
End bitvec16PayloadMap.

Module KTranslate := Translate TheDimensionality Neurons Outputs 
                               bitvec16Type bitvec2Type
                               bitvec16PayloadMap bitvec2PayloadMap.
Import KTranslate. Import TheNet.
Import F. Import NETEval. Import NET.

Definition X := AxVec TheDimensionality.n (bitvec 16).
Definition XFin := AxVec_finType TheDimensionality.n bitvec16FinType.t.
Definition Y := 'I_Outputs.n.
Definition Hypers := unit.
Definition Params := Kernel.t TheDimensionality.n Neurons.n Outputs.n bitvec16Type.t bitvec2Type.t.
Definition ParamsFin := KernelFintype.t TheDimensionality.n Neurons.n Outputs.n bitvec16FinType.t bitvec2FinType.t.

Definition InputEnv_of_X (img:X) : NETEval.InputEnv.t :=
  KTranslate.TheNet.F.NETEval.NET.InputEnv.of_list
    (List.map (fun x_bits =>
                 let: (x,bits) := x_bits in 
                 (x, bitvec16PayloadMap.f bits))
              (zip InputEnv.Ix.enumerate_t (AxVec_to_list img))).

Definition Y_of_OutputIx (ix:Output.Ix.t) : Y := Output.Ix.Ordinal_of_t ix.

Definition logits (p:Params) (img:X) :=
  TheNet.F.seval
    (translate_kernel p)
    (TheNet.F.Forest.of_list
    (combine (Forest.Ix.enumerate_t) (rev outputs)))
    (InputEnv_of_X img).

Definition predict (h:Hypers) (p:Params) (img:X) : Y :=
  let: outs := logits p img
  in Y_of_OutputIx (Output.argmax Dlt_bool outs).

(* For printing/debugging. *)
Definition logits' (p:Params) (img:X) :=
  map snd (Output.to_dense_list (logits p img)).
Definition predict' (h:Hypers) (p:Params) (img:X) : nat :=
  let: outs := logits p img in
  Output.Ix.val (Output.argmax Dlt_bool outs).
Definition logits_predictions (kernel : Params) (batch : list (X * Y)) :=
  (map (fun x_y => let: (x, y) := x_y in logits' kernel x) batch,
   map (fun x_y => let: (x, y) := x_y in predict' tt kernel x) batch).
Definition print_logits_predictions kernel batch :=
  let (ls, ps) := logits_predictions kernel batch in
  let ls' := map (print_newline ∘ map (print_space ∘ print_DRed)) ls in
  let ps' := map (print_space ∘ print_nat) ps in
  (ls', ps').
Module KPrint := PrintKernel TheDimensionality Neurons Outputs
                             bitvec16Type bitvec2Type
                             bitvec16PayloadMap bitvec2PayloadMap.

Open Scope list_scope.
Notation "\'i\' ( x )":=(NIn x) (at level 65).
Notation "\'r\' ( x )":=(NReLU x) (at level 65).
Notation "\'c\' ( x )":=(NComb x) (at level 65).
Notation "\'V\' ( x )":=(@AxVec_of_list _ _ x) (at level 65).
Notation "\'T\'":=(true) (at level 65).
Notation "\'F\'":=(false) (at level 65).
""".format(IN, IN, NEURONS, NEURONS, OUT, OUT, N_W)

def the_postamble():
    return """
Definition m : nat := 200 * 1000. (*240000 causes stack overflow*)
Lemma m_gt0 : 0 < m. Proof. by []. Qed.

Definition mtest : nat := 40 * 1000.
Lemma mtest_gt0 : 0 < mtest. Proof. by []. Qed.

Definition tf_learner
  : Learner.t XFin Y Hypers ParamsFin
  := OracleLearner kernel predict. 

Notation tf_main :=
  (@oracular_main XFin [finType of Y] ParamsFin Hypers tf_learner tt m m_gt0 (fun _ => kernel)).

Notation tf_main_holdout :=
  (@oracular_main_holdout
     XFin [finType of Y] ParamsFin Hypers tf_learner tt
     m m_gt0 mtest mtest_gt0 (fun _ _ => kernel)).

Notation accuracy_holdout := (@accuracy XFin [finType of Y] ParamsFin Hypers tf_learner tt mtest).

Notation accuracy := (@accuracy XFin [finType of Y] ParamsFin Hypers tf_learner tt m).

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist.
Require Import QArith Reals Rpower Ranalysis Fourier.

Section tf_bound.
  Variables
    (d:XFin*Y -> R) 
    (d_dist : big_sum (enum [finType of XFin*Y]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : ParamsFin, mutual_independence (m:=m) d (accuracy p))
    (not_perfectly_learnable : 
      forall p : ParamsFin, 0 < expVal d m_gt0 accuracy p < 1).

Lemma tf_main_bound (eps:R) (eps_gt0 : 0 < eps) (init:ParamsFin) :
  tf_main d eps init (fun _ => 1) <= 
  INR (2 ^ (4 * 16 + 10 * 784 * 2 + 10 * 10 * 2)) * exp (-2%R * eps^2 * mR m).
Proof.
  rewrite -card_bitvec2_EMNIST_10_KernelFinType; apply: Rle_trans; last first.
  { apply oracular_main_bound => //; first by apply: d_dist. }
  apply: Rle_refl.
Qed.
End tf_bound.

Section tf_holdout_bound.
  Variables
    (d:XFin*Y -> R) 
    (d_dist : big_sum (enum [finType of XFin*Y]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : ParamsFin, mutual_independence (m:=mtest) d (accuracy_holdout p))
    (not_perfectly_learnable : 
      forall p : ParamsFin, 0 < expVal d mtest_gt0 accuracy_holdout p < 1).

Lemma tf_main_holdout_bound (eps:R) (eps_gt0 : 0 < eps) (init:ParamsFin) :
  tf_main_holdout d eps init (fun _ => 1) <= exp (-2%R * eps^2 * mR mtest).
Proof. by apply: oracular_main_holdout_bound. Qed.
End tf_holdout_bound.
"""

# Given the min and max quantization parameters, compute the
# corresponding shift and scale values.
def compute_shift_scale(min_b, max_b, num_bits):
    shift = min_b
    scale = (max_b - min_b) / (2**num_bits - 1)
    return shift, scale

# NOTE: Switches endianness
def to_bit_vector(x):
    return build_vector(';', [coqbool_of_bitchar(i) for i in x][::-1])

def build_kernel(shift0, scale0, shift1, scale1, w0, w1):
    return '((%s, %s),\n(%s, %s),\n%s,\n%s)' \
        % (shift0, scale0, shift1, scale1, w0, w1)

# Produce the output Coq file
def to_coq(IN, NEURONS, OUT, kernel):
    out = ''
    out += the_preamble(IN, NEURONS, OUT)
    out += '\nDefinition kernel : Params := ' + kernel + '.\n' 
    out += the_postamble()
    return out

# Load the weights
weights, bounds = load_weights_bounds(path)

w0 = weights[0]
w1 = weights[1]
min0 = bounds[0]
max0 = bounds[1]
min1 = bounds[2]
max1 = bounds[3]

shift0, scale0 = compute_shift_scale(min0, max0, N_W)
shift1, scale1 = compute_shift_scale(min1, max1, N_W)

print(shift0)
print(scale0)
print(shift1)
print(scale1)

shift0_bits = float_to_bin(np.float16(shift0), N_SS)
scale0_bits = float_to_bin(np.float16(scale0), N_SS)
shift1_bits = float_to_bin(np.float16(shift1), N_SS)
scale1_bits = float_to_bin(np.float16(scale1), N_SS)


print(w0.shape)
print(w1.shape)

w0_bits = []
for i in range(w0.shape[1]):
    w = [x.zfill(N_W) for x in w0[:,i]]
    bvecs = [to_bit_vector(x) for x in w]
    vec = build_vector(';\n', bvecs)
    w0_bits.append(vec)
print(np.array(w0_bits).shape)
w0_vec = build_vector(';\n', w0_bits)

w1_bits = []
for i in range(w1.shape[1]):
    w = [x.zfill(N_W) for x in w1[:,i]]
    bvecs = [to_bit_vector(x) for x in w]
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
IN = w0.shape[0]

num_neurons = w1.shape[0]

src = to_coq(IN, num_neurons, NUM_CLASSES, kernel)

# Write it to file
with open("qout.v", "w") as f:
    f.write(src)
