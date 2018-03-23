Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic net bitnet.

Module TheDimensionality. Definition n : nat := N.to_nat 3. 
Lemma n_gt0 : (0 < N.to_nat 3)%nat. by []. Qed. End TheDimensionality.
Module Params. Definition n : nat := N.to_nat 3. 
Lemma n_gt0 : (0 < N.to_nat 3)%nat. by []. Qed. End Params.
Module Outputs. Definition n : nat := 2. Lemma n_gt0 : (0 < 2)%nat. by []. Qed. End Outputs.
Module TheNet := DyadicFloat16Net TheDimensionality Params Outputs.
Import TheNet. Import F. Import FT. Import NETEval. Import NET.
Import DyadicFloat16. (*for bits_to_bvec*)

Definition bvec16_neg2p0 := bits_to_bvec [15%N;14%N].
Definition bvec16_2p0 := bits_to_bvec [14%N].
Definition bvec16_1p0 := bits_to_bvec [13%N;12%N;11%N;10%N].
Definition bvec16_0p0  := BitVec.of_fun (fun ix => BO).
Definition bvec16_0p5  := bits_to_bvec [13%N;12%N;11%N].

Open Scope list_scope.
Notation "'i' ( x )":=(NIn x) (at level 65).
Notation "'r' ( x )":=(NReLU x) (at level 65).
Notation "'c' ( x )":=(NComb x) (at level 65).
Program Definition x_0 : input_var := @InputEnv.Ix.mk 0 _.
Program Definition x_1 : input_var := @InputEnv.Ix.mk 1 _.
Program Definition x_2 : input_var := @InputEnv.Ix.mk 2 _.
Program Definition w_0 : param_var := @ParamEnv.Ix.mk 0 _.
Program Definition w_1 : param_var := @ParamEnv.Ix.mk 1 _.
Program Definition w_2 : param_var := @ParamEnv.Ix.mk 2 _.
(* THETA = (1 -2 2) *)
Definition theta := ParamEnv.of_fun (fun ix => match ix with ParamEnv.Ix.mk ix' _ =>
  if N.eqb ix' 0 then bvec16_1p0 else
  if N.eqb ix' 1 then bvec16_neg2p0 else
  if N.eqb ix' 2 then bvec16_2p0 else    
    (bits_to_bvec []) end).
Definition n_0_0:=i(x_0).
Definition n_0_1:=i(x_1).
Definition n_0_2:=i(x_2).
Definition n_1_0:=c((w_0,n_0_0)::(w_1,n_0_1)::(w_2,n_0_2)::nil).
Definition n_1_1:=c((w_0,n_0_0)::(w_0,r(n_1_0))::nil).
Definition outputs:=r(n_1_1)::nil.
(* RHO = (0.5 0.5 0.5) *)
Definition rho := InputEnv.of_fun (fun ix => match ix with InputEnv.Ix.mk ix' _ =>
  if N.eqb ix' 0 then bvec16_0p5 else
  if N.eqb ix' 1 then bvec16_0p5 else
  if N.eqb ix' 2 then bvec16_0p5 else      
    (bits_to_bvec []) end).

Definition forest :=
  Forest.of_fun (fun ix => 
    if N.eqb (Forest.Ix.val ix) 0 then r(n_1_1) else r(n_1_0)).
    
Definition go := TheNet.seval theta forest rho.

Extraction "test.ml" go.
