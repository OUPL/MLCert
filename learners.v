Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.
Require Import Extraction.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist.

Require Import MLCert.float32.

Module Learner.
  Record t (A B Hypers Params : Type) :=
    mk { predict : Hypers -> Params -> A -> B;
         update : Hypers -> A*B -> Params -> Params }.
End Learner.

Section semantics.
  Variables A B Params : finType. 
  Variable Hypers : Type.
  Variable learner : Learner.t A B Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Definition C (t:Type) := (t -> R) -> R.

  Definition sample (d:A*B -> R) : C (training_set A B m) :=
    fun f => big_sum (enum (training_set A B m)) (fun T => 
      (prodR (fun _:'I_m => d)) T * f T).

  Definition learn_func (init:Params) (T:training_set A B m) := 
    foldr (fun i p => 
      Learner.update learner h (T i) p) init (enum 'I_m).

  Definition learn (init:Params) (T:training_set A B m) : C (Params) :=
    fun f => f (learn_func init T).

  Definition seq (t1 t2 : Type) (c1:C t1) (c2:t1 -> C t2) : C t2 :=
    fun f => c1 (fun t1 => c2 t1 f).

  Definition observe (t:Type) (p:pred t) : t -> C t :=
    fun t f => if p t then f t else 0.

  Definition accuracy := accuracy01 (m:=m) (Learner.predict learner h).

  Definition post (d:A*B -> R) (eps:R) 
      (pT : Params * training_set A B m) : bool :=
    let: (p, T) := pT in 
    Rlt_le_dec (expVal d m_gt0 accuracy p + eps) (empVal accuracy T p).

  Notation "x <-- e1 ; e2" := (seq e1 (fun x => e2)) 
    (at level 100, right associativity).

  Definition main (d:A*B -> R) (eps:R) (init:Params) 
    : C (Params * training_set A B m) :=
    T <-- sample d;
    p <-- learn init T;
    observe (post d eps) (p,T).

  Variables 
    (d:A*B -> R) 
    (d_dist : big_sum (enum [finType of A*B]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : Params, mutual_independence d (accuracy p))
    (not_perfectly_learnable : 
      forall p : Params, 0 < expVal d m_gt0 accuracy p < 1).

  Lemma main_bound (eps:R) (eps_gt0 : 0 < eps) (init:Params) :
    main d eps init (fun _ => 1) <= 
    INR #|Params| * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite /main/seq/sample/learn/observe/=big_sum_pred2; apply: Rle_trans; last first.
    { apply chernoff_bound_accuracy01 with (d:=d) (learn:=learn_func init) => //.
      { move => p; apply: mut_ind. }
      move => p; apply: not_perfectly_learnable. }
    apply: big_sum_le => c; rewrite /in_mem Rmult_1_r /= => _; apply: Rle_refl.
  Qed.
End semantics.