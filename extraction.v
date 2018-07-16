Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Axiom HsListVec : forall (m:nat) (t:Type), Type.
Axiom HsListVec_get : forall (m:nat) (t:Type) (i:'I_m) (l:HsListVec m t), t.
(*Axiom HsListVec_upd : forall (m:nat) (t:Type) (i:'I_m) (x:t) (l:HsListVec m t), HsListVec m t.*)

Extract Constant HsListVec "t" => "[t]".
Extract Constant HsListVec_get => 
  "(\_ i l -> 
     let nat2int O = 0
         nat2int (S n) = (Prelude.+) 1 (nat2int n)
     in (Prelude.!!) l (nat2int i))".

Extract Constant R => "Prelude.Double".