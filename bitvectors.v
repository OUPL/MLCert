Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import Reals Rpower.
Require Import List. Import ListNotations.

Require Import MLCert.axioms.

Definition bitvec (n:nat) := AxVec n bool.

Lemma bitvec_finite : forall (n:nat), Finite.class_of (bitvec n).
Proof. move => n; apply: AxVec_finite. Defined.

Definition bitvec_finType (n:nat) : finType := Finite.Pack (bitvec_finite n) .

Lemma bitvec_card m : #|bitvec_finType m| = 2^m.
Proof.
  rewrite /bitvec_finType/=/bitvec (@AxVec_card m 1 bool_finType) => //=.
  { by rewrite muln1. }
  by rewrite card_bool.
Qed.

Definition bitvec_to_list (n:nat) (v:bitvec n) : list bool := AxVec_to_list v.

(*The following conversion routines, from bitvec to a sparse representation 
  as list N.t, assumes that bitvecs are ordered in little-endian style, with 
  least significant bits first:  
    b_0 :: b_1 :: ... :: b_(n-1) *)

Fixpoint bitvec_to_sparse_list_aux (n:nat) (l:list bool) (acc:list N.t) : list N.t :=
  match l with
  | nil => acc
  | b :: nil => if b then N.of_nat n :: acc else acc
  | b :: l' => 
    let acc' := if b then N.of_nat n :: acc else acc in
    bitvec_to_sparse_list_aux (S n) l' acc'
  end.

Definition bitvec_to_sparse_list n (v:bitvec n) : list N.t :=
  bitvec_to_sparse_list_aux 0 (bitvec_to_list v) nil.
