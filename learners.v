Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist.

Require Import MLCert.monads.

Module Learner.
  Record t (A B Hypers Params : Type) :=
    mk { predict : Hypers -> Params -> A -> B;
         update : Hypers -> A*B -> Params -> Params }.
End Learner.

Section extractible_semantics.
  Variable A B Params Hypers : Type.
  Variable learner : Learner.t A B Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable epochs : nat.
  Variable training_set : Type.
  Variable training_set_get : 'I_m -> training_set -> A*B.
  Variable u : Type.

  Notation C t := (Cont u t).
  
  Variable sample : (A*B -> R) -> C training_set.

  Definition learn_func (init:Params) (T:training_set) :=
    foldr (fun epoch p_epoch => 
      foldr (fun i p => 
        Learner.update learner h (training_set_get i T) p) 
        p_epoch (enum 'I_m))
      init (enum 'I_epochs).

  Definition learn (init:Params) (T:training_set) : C (Params) :=
    fun f => f (learn_func init T).

  Definition extractible_main (d:A*B -> R) (init:Params)
    : C (Params * training_set) :=
    T <-- sample d;
    p <-- learn init T;
    ret (p, T).
End extractible_semantics.

Section semantics.
  Variables A B Params : finType. 
  Variable Hypers : Type.
  Variable learner : Learner.t A B Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.
  Variable epochs : nat.

  Notation C := (@Cont R).

  Definition semantic_sample (d:A*B -> R) : C (training_set A B m) :=
    fun f => big_sum (enum (training_set A B m)) (fun T => 
      (prodR (fun _:'I_m => d)) T * f T).

  Definition semantic_sample_get (i:'I_m) (T:training_set A B m) : A*B := T i.

  Definition observe (t:Type) (p:pred t) : t -> C t :=
    fun t f => if p t then f t else 0.

  Definition accuracy := accuracy01 (m:=m) (Learner.predict learner h).

  Definition post (d:A*B -> R) (eps:R) 
      (pT : Params * training_set A B m) : bool :=
    let: (p, T) := pT in 
    Rlt_le_dec (expVal d m_gt0 accuracy p + eps) (empVal accuracy T p).

  Definition semantic_main (d:A*B -> R) (init:Params) := 
    extractible_main learner h epochs semantic_sample_get semantic_sample d init.

  Definition main (d:A*B -> R) (eps:R) (init:Params) 
    : C (Params * training_set A B m) :=
    pT <-- semantic_main d init;
    let: (p,T) := pT in
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
    rewrite /main/semantic_main/extractible_main/semantic_sample/learn/observe/=.
    rewrite /Cbind/Cret.
    rewrite big_sum_pred2; apply: Rle_trans; last first.
    { apply chernoff_bound_accuracy01 
        with (d:=d) (learn:=learn_func learner h epochs semantic_sample_get init) => //.
      { move => p; apply: mut_ind. }
      move => p; apply: not_perfectly_learnable. }
    apply: big_sum_le => c; rewrite /in_mem Rmult_1_r /= => _; apply: Rle_refl.
  Qed.
End semantics.