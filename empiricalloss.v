
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic.
Require Import net bitnet out data.

Import out.TheNet.
Import TheNet. Import F. Import FT. Import NETEval. Import NET.

Eval compute in (length samples).

Definition train_set := combine samples labels.

(* This hangs *)
(* Eval compute in (hd_error samples). *)

Import DyadicFloat16. (*for bits_to_bvec*)
Definition bvec := bits_to_bvec [0%N; 1%N].
(* This doesn't compute properly *)
Eval compute in bvec.
