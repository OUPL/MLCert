Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

(** Axioms. Extraction schemes are language specific, and can be
 found in files: 
 - extraction_hs.v (Haskell)
 - extraction_ocaml.v (OCaml)
 The following files contain addditional axioms/schemes: 
 - float32.v *)

(*Axiomatized length-indexed vectors.

  [NOTE: Axiomatization of AxVec]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We axiomatize some operations on AxVec (e.g., AxVec_to_list) 
  but don't assume anything about the behavior of these axiomatized 
  operations. We do, however, assume facts about the cardinality of 
  AxVec, given it's instantiated at a finite type.*)

Require Import Vector.

Axiom AxVec : forall (n:nat) (t:Type), Type.
Axiom AxVec_to_list : forall (n:nat) (t:Type), AxVec n t -> list t.

Axiom AxVec_finite : forall (n:nat) (t:finType), Finite.class_of (AxVec n t).
Definition AxVec_finType (n:nat) (t:finType) : finType :=
  Finite.Pack (AxVec_finite n t) (AxVec n t).
Axiom AxVec_card : forall m n (t:finType), #|t| = 2^n -> #|AxVec_finType m t| = 2^(m*n).

Axiom AxVec_map : forall (n:nat) (s t:Type), (s -> t) -> AxVec n s -> AxVec n t.
Axiom AxVec_cons: forall (n:nat) (t:Type), t -> AxVec n t -> AxVec (S n) t.
Axiom AxVec_tail: forall (n:nat) (t:Type), AxVec (S n) t -> AxVec n t.

Definition AxMat A n m := AxVec n (AxVec m A).
Definition matrix_map {A B n m} (f : A -> B) : AxMat A n m -> AxMat B n m :=
  AxVec_map (AxVec_map f).
