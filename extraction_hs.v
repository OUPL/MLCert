Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

Require Import MLCert.axioms.

(** Haskell-specific extraction schemes *)

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].

Extract Constant R => "Prelude.Double". (*NOTE: We extract no R operations, just the type.*)

Extract Constant AxVec "t" => "[t]".
(*Why is HsListVec_to_list essentially the identity function? Because we extract 
  Coq lists to Haskell lists (see the 'Extract Inductive list' directive above).*)
Extract Constant AxVec_to_list => "(\_ l -> l)".

(*AxVec Tests*)
(* Require Import List. *)
(* Fixpoint sum_natlist (l:list nat) : nat := *)
(*   match l with *)
(*   | nil => 0 *)
(*   | cons x l' => x + sum_natlist l' *)
(*   end. *)
(* Definition sum_AxVec (n:nat) (v:AxVec n nat) : nat := *)
(*   sum_natlist (AxVec_to_list v). *)
(* Extraction Language Haskell. *)
(* Extraction "hs/AxVec.hs" sum_AxVec. *)
(*END AxVec Tests*)
