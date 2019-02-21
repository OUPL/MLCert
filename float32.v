Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Reals Rpower.
Require Import Extraction.

Require Import MLCert.axioms MLCert.extraction_hs.

(*Axiomatized 32-bit floating point numbers, together with cardinality axioms. 
  Currently Haskell-only: OCaml's float is double-precision by default; nor does 
  the OCaml standard support a single-precision 32-bit FP type.*)

(*32-bit floating-point numbers*)
Axiom float32 : Type. 
Axiom float32_finite : Finite.class_of float32.
Definition float32_finType : finType := Finite.Pack float32_finite float32.
Axiom float32_card : #|float32_finType| = 2^32.

Extract Constant float32 => "Prelude.Float".

(*Arrays of 32-bit floats, implemented as AxVec's*)
Definition float32_arr (n:nat) := AxVec n float32. (*size-indexed float32 arrays*)
Lemma float32_arr_finite : forall n:nat, Finite.class_of (float32_arr n).
Proof. move => n; rewrite /float32_arr; apply: (AxVec_finite n float32_finType). Defined.
Definition float32_arr_finType (n:nat) : finType :=
  Finite.Pack (float32_arr_finite n) (float32_arr n).
Lemma float32_arr_card : forall n, #|float32_arr_finType n| = 2^(n*32).
Proof. by move => n; move: (@AxVec_card n 32 float32_finType float32_card) => /= <-. Qed.

(*Axiomatized arithmetic expressions over float32's and float arrays*)
Axiom f32_0 : float32.
Axiom f32_1 : float32.
Axiom f32_opp : float32 -> float32.
Axiom f32_gt : float32 -> float32 -> bool.
Axiom f32_add : float32 -> float32 -> float32.
Axiom f32_mult : float32 -> float32 -> float32.
Axiom f32_div : float32 -> float32 -> float32.
Axiom f32_init : forall (n:nat)(init:float32), float32_arr n.
Axiom f32_map : forall (n:nat)(f:float32->float32)(a:float32_arr n), float32_arr n.
Axiom f32_mapM : forall (M:Type->Type)(n:nat)(f:float32->M float32)(a:float32_arr n), M (float32_arr n).
Axiom f32_map2 : forall (n:nat)(f:float32->float32->float32)(a b:float32_arr n), float32_arr n.
Axiom f32_fold2 : forall (T:Type)(n:nat)(t0:T)(f:float32->float32->T->T)(a1 a2:float32_arr n), T.

Extract Constant f32_0 => "(0.0 :: Prelude.Float)".
Extract Constant f32_1 => "(1.0 :: Prelude.Float)".
Extract Constant f32_opp => "(\f -> - f)".
Extract Constant f32_gt => "(\f1 f2 -> (Prelude.>) f1 f2)".
Extract Constant f32_add => "(\f1 f2 -> (Prelude.+) f1 f2)".
Extract Constant f32_mult => "(\f1 f2 -> (Prelude.*) f1 f2)".
Extract Constant f32_div => "(\f1 f2 -> (Prelude./) f1 f2)".
Extract Constant f32_init =>
  "(\n init -> case n of 
                 O -> []
                 S n1 -> init : f32_init n1 init)".
Extract Constant f32_map => "(\_ f a -> Prelude.map f a)".
Extract Constant f32_mapM => "(\_ f a -> Prelude.mapM f a)".
Extract Constant f32_map2 => "(\_ f a1 a2 -> Prelude.map (\(x,y) -> f x y) (Prelude.zip a1 a2))".
Extract Constant f32_fold2 => "(\_ t f a1 a2 -> Prelude.foldl (\acc (x, y) -> f x y acc) t (Prelude.zip a1 a2))".

(*Notation and derived operations*)
Notation "0" := (f32_0) : f32_scope.
Notation "1" := (f32_1) : f32_scope.
Notation "2" := (f32_add f32_1 f32_1) : f32_scope.
Infix ">" := (f32_gt) : f32_scope.
Infix "+" := (f32_add) : f32_scope. 
Infix "*" := (f32_mult) : f32_scope.
Infix "/" := (f32_div) : f32_scope.

Definition neg1 : float32 := f32_opp f32_1.
Definition float32_of_bool (b:bool) := if b then f32_1 else neg1.
Coercion float32_of_bool : bool >-> float32.

Section f32_definitions.
  Open Scope f32_scope.

  Definition f32_dot (n:nat) (a1 a2:float32_arr n) : float32 :=
    f32_fold2 0 (fun x1 x2 sum => (x1 * x2) + sum) a1 a2.
End f32_definitions.
