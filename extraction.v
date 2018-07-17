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

