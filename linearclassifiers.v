Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import NArith.
Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.float32 MLCert.learners MLCert.extraction.

Section LinearThresholdClassifier.
  Variable n : nat. (*the dimensionality*)
  Variable theta : float32. (*the threshold*)

  Definition A := float32_arr n. (*examples*)
  Definition B := bool. (*labels*)
  Definition Weights := float32_arr n.
  Definition Bias := float32.
  Definition Params := (Weights * Bias)%type.

  Section predict.
    Open Scope f32_scope.
    Definition predict (p : Params) (a : A) : B :=
      let: (w, b) := p in
      f32_dot w a + b > theta.
  End predict.
End LinearThresholdClassifier.

Module Perceptron.
  Section Learner.
    Variable n : nat.
    Notation A := (A n).
    Notation B := B.
    Notation Params := (Params n).

    Record Hypers : Type :=
      mkHypers { 
        alpha : float32;
        theta : float32
      }.

    Open Scope f32_scope.

    Definition update (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: (example, label) := example_label in
      let: predicted_label := predict (theta h) p example in
      if Bool.eqb predicted_label label then p
      else let: (w, b) := p in
           (f32_map2 (fun x1 x2 => x1 + (alpha h)*label*x2) w example, b+label).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun h => @predict n (theta h))
        update.
  End Learner.
End Perceptron.

Require Import Reals Fourier.
Require Import OUVerT.bigops OUVerT.dist OUVerT.chernoff OUVerT.learning.

Section PerceptronGeneralization.
  Variable n : nat. (*The dimensionality*)
  Notation A := (float32_arr_finType n).
  Notation B := bool_finType.
  Variable d : A * B -> R.
  Variable d_dist : big_sum (enum [finType of A * B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.

  Variable hypers : Perceptron.Hypers.

  (*accuracy is 0-1 accuracy applied to Perceptron's prediction function*)
  Notation Params := [finType of A * float32_finType].
  Definition accuracy := 
    @accuracy01 A _ m Params (Learner.predict (Perceptron.Learner n) hypers).

  Lemma card_Params : INR #|Params| = 2^(n*32 + 32).
  Proof. by rewrite pow_add card_prod mult_INR float32_card float32_arr_card !pow_INR. Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 accuracy p < 1)
    (mut_ind : forall p : Params, mutual_independence d (accuracy p)).

  Lemma perceptron_bound eps (eps_gt0 : 0 < eps) init : 
    @main A B Params Perceptron.Hypers (Perceptron.Learner n) 
      hypers m m_gt0 d eps init (fun _ => 1) <=
    2^(n*32 + 32) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -card_Params.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End PerceptronGeneralization.

Section PerceptronExtraction.
  Variable n : nat. (*The dimensionality*)
  Notation A := (float32_arr n).
  Notation B := bool.
  Variable d : A * B -> R.

  Variable m : nat. (*The number of training samples*)

  Notation Params := ((A * float32)%type).

  Variable hypers : Perceptron.Hypers.

  Definition perceptron := 
    @extractible_main A B Params Perceptron.Hypers 
      (Perceptron.Learner n) hypers 
      m (HsListVec m (A*B)) (@HsListVec_get m (A*B)).
End PerceptronExtraction.
Extraction Language Haskell.

Extract Constant R => "Prelude.Double".
Extraction "hs/Perceptron.hs" perceptron.