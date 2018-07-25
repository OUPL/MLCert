Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

Require Import MLCert.monads.

(** Axioms together with extraction schemes. 
 The following files contain addditional axioms/schemes: 
 - float32.v *)

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].

Extract Constant R => "Prelude.Double". (*NOTE: We extract no R operations, just the type.*)

(*Axiomatized length-indexed vectors, implemented as Haskell lists. 

  [NOTE: Axiomatization of HsListVec]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We axiomatize some operations on HsListVec (e.g., HsListVec_to_list) 
  but don't assume anything about the behavior of these axiomatized 
  operations. We do, however, assume facts about the cardinality of 
  HsListVec, given it's instantiated at a finite type.*)

Axiom HsListVec : forall (n:nat) (t:Type), Type.
Axiom HsListVec_to_list : forall (n:nat) (t:Type), HsListVec n t -> list t.
Axiom HsListVec_finite : forall (n:nat) (t:finType), Finite.class_of (HsListVec n t).
Definition HsListVec_finType (n:nat) (t:finType) : finType :=
  Finite.Pack (HsListVec_finite n t) (HsListVec n t).
Axiom HsListVec_card : forall m n (t:finType), #|t| = 2^n -> #|HsListVec_finType m t| = 2^(m*n).

Extract Constant HsListVec "t" => "[t]".
(*Why is HsListVec_to_list essentially the identity function? Because we extract 
  Coq lists to Haskell lists (see the 'Extract Inductive list' directive above).*)
Extract Constant HsListVec_to_list => "(\_ l -> l)".

(*HsListVec Tests*)
(* Require Import List. *)
(* Fixpoint sum_natlist (l:list nat) : nat := *)
(*   match l with *)
(*   | nil => 0 *)
(*   | cons x l' => x + sum_natlist l' *)
(*   end. *)
(* Definition sum_HsListVec (n:nat) (v:HsListVec n nat) : nat := *)
(*   sum_natlist (HsListVec_to_list v). *)
(* Extraction Language Haskell. *)
(* Extraction "hs/HsListVec.hs" sum_HsListVec. *)
(*END HsListVec Tests*)
