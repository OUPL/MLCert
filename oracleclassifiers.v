Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import NArith.
Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.learners.

Section OracleLearner.
  Variables X Y Hypers Params : Type.
  Variable oracular_params : Params.
  Variable predict : Hypers -> Params -> X -> Y.
  
  Definition OracleLearner : Learner.t X Y Hypers Params :=
    Learner.mk predict (fun _ _ _ => oracular_params).
End OracleLearner.

Require Import Reals Fourier.
Require Import OUVerT.bigops OUVerT.dist OUVerT.chernoff OUVerT.learning.

Section OracleGeneralization.
  Variables X Y : finType.
  Variables (Hypers : Type) (Params : finType).
  Variable oracular_params : Params.
  Variable predict : Hypers -> Params -> X -> Y.
  Notation OracleLearner := (@OracleLearner X Y Hypers Params oracular_params predict).
  
  Variable d : X * Y -> R.
  Variable d_dist : big_sum (enum [finType of X * Y]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.

  Variable epochs : nat.

  Variable hypers : Hypers.

  Definition accuracy := @accuracy01 X _ m Params (predict hypers).

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 accuracy p < 1)
    (mut_ind : forall p : Params, mutual_independence d (accuracy p)).

  Lemma oracle_bound eps (eps_gt0 : 0 < eps) init : 
    @main X Y Params Hypers OracleLearner
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    INR #|Params| * exp (-2%R * eps^2 * mR m).
  Proof.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End OracleGeneralization.
