Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

Require Import MLCert.axioms.

(** OCaml-specific extraction schemes *)

Extraction Language OCaml.

Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].

Extract Constant R => "float". (*NOTE: We extract no R operations, just the type.*)

Extract Constant AxVec "'t" => "('t list)".
(*Why is AxVec_to_list the identity function? Because we extract Coq lists
  to OCaml lists (see the 'Extract Inductive list' directive above).*)
Extract Constant AxVec_to_list => "(fun _ l -> l)".
Extract Constant AxVec_of_list => "(fun _ l -> l)".

(* (*AxVec Tests*) *)
(* Require Import List. *)
(* Fixpoint sum_natlist (l:list nat) : nat := *)
(*   match l with *)
(*   | nil => 0 *)
(*   | cons x l' => x + sum_natlist l' *)
(*   end. *)
(* Definition sum_AxVec (n:nat) (v:AxVec n nat) : nat := *)
(*   sum_natlist (AxVec_to_list v). *)
(* Extraction "ocaml/AxVec.ml" sum_AxVec. *)
(* (*END AxVec Tests*) *)
