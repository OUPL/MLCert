Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import NArith.
Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.float32 MLCert.learners MLCert.extraction_hs MLCert.monads.

Section LinearThresholdClassifier.
  Variable n : nat. (*the dimensionality*)

  Definition A := float32_arr n. (*examples*)
  Definition B := bool. (*labels*)
  Definition Weights := float32_arr n.
  Definition Bias := float32.
  Definition Params := (Weights * Bias)%type.

  Section predict.
    Open Scope f32_scope.
    Definition predict (p : Params) (a : A) : B :=
      let: (w, b) := p in
      f32_dot w a + b > 0.
  End predict.
End LinearThresholdClassifier.

Section KernelClassifier.
  Variable n : nat. (*the dimensionality*)
  Variable m : nat. (*#examples*)

  Definition Ak := ('I_m * float32_arr n)%type. (*examples*)
  Definition Bk := bool. (*labels*)
  Context {training_set} `{Foldable training_set (Ak * Bk)}.
  Definition KernelParams := (training_set * float32_arr m)%type.

  Section predict.
    Open Scope f32_scope.

    Definition kernel_predict (w : KernelParams) (x : Ak) : Bk :=
      let T := w.1 in 
      foldable_foldM
        (fun xi_yi r =>
           let: ((i, xi), yi) := xi_yi in
           let: (j, xj) := x in 
           let: wi := f32_get i w.2 in 
           r + (float32_of_bool yi) * wi * f32_dot xi xj)
        0 T > 0.
  End predict.
End KernelClassifier.

Module Perceptron.
  Section Learner.
    Variable n : nat.
    Notation A := (A n).
    Notation B := B.
    Notation Params := (Params n).

    Record Hypers : Type :=
      mkHypers { 
        alpha : float32;
      }.

    Open Scope f32_scope.

    Definition update (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: (example, label) := example_label in
      let: predicted_label := predict p example in
      if Bool.eqb predicted_label label then p
      else let: (w, b) := p in
           (f32_map2 (fun x1 x2 => x1 + (alpha h)*label*x2) w example, b+label).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun h => @predict n)
        update.
  End Learner.
End Perceptron.

Module KernelPerceptron.
  Section Learner.
    Variable n : nat. (*the dimensionality*)
    Variable m : nat. (*#examples*)
    Notation A := (Ak n m).
    Notation B := Bk.
    Context {training_set} `{F:Foldable training_set (A * B)}.        
    Definition Params := @KernelParams m training_set.

    Record Hypers : Type := mkHypers { }.

    Open Scope f32_scope.

    Definition kernel_update (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: ((i, example), label) := example_label in 
      let: predicted_label := kernel_predict p (i, example) in
      if Bool.eqb predicted_label label then p
      else (p.1, f32_upd i (f32_get i p.2 + 1) p.2).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict n m training_set F)
        kernel_update.
  End Learner.
End KernelPerceptron.

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

  Variable epochs : nat.

  Variable hypers : Perceptron.Hypers.

  (*accuracy is 0-1 accuracy applied to Perceptron's prediction function*)
  Notation Params := [finType of A * float32_finType].
  Definition accuracy := 
    @accuracy01 A _ m Params (Learner.predict (Perceptron.Learner n) hypers).

  Lemma card_Params : INR #|Params| = 2^(n*32 + 32).
  Proof. by rewrite pow_add card_prod mult_INR float32_card float32_arr_card !pow_INR. Qed.

  Variable 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 accuracy p < 1).

  Lemma perceptron_bound eps (eps_gt0 : 0 < eps) init : 
    @main A B Params Perceptron.Hypers (Perceptron.Learner n) 
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    2^(n*32 + 32) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -card_Params.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End PerceptronGeneralization.

Section KernelPerceptronGeneralization.
  Variable n : nat. (*The dimensionality*)
  Variable m : nat. (*#examples*)
  Notation A := [finType of 'I_m * float32_arr_finType n].
  Notation B := bool_finType.
  Variable d : A * B -> R.
  Variable d_dist : big_sum (enum [finType of A * B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m_gt0 : (0 < m)%nat.

  Variable epochs : nat.

  Variable hypers : KernelPerceptron.Hypers.

  (*Represent the training set as a one-dimensional (flattened) float array.*)
  Definition training_set := float32_arr_finType (m*n).
  Context {H: Foldable training_set (A * B)}.

  Notation Params := [finType of {:training_set * float32_arr_finType m}].
  Definition Kaccuracy := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptron.Learner n m training_set H) hypers).

  Lemma Kcard_Params : INR #|Params| = 2 ^ (m*n*32 + m*32).
  Proof.
    rewrite /training_set card_prod !float32_arr_card.
    rewrite mult_INR !pow_INR /= pow_add //.
  Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 Kaccuracy p < 1)
    (mut_ind : forall p : Params, mutual_independence d (Kaccuracy p)).

  Lemma Kperceptron_bound eps (eps_gt0 : 0 < eps) init : 
    @main A B Params KernelPerceptron.Hypers 
      (@KernelPerceptron.Learner n m training_set H)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    2^(m*n*32 + m*32) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralization.

Section PerceptronExtraction.
  Variable n : nat. (*The dimensionality*)
  Notation A := (float32_arr n).
  Notation B := bool.
  Variable d : A * B -> R.

  Variable m : nat. (*The number of training samples*)
  Variable epochs : nat.

  Notation Params := ((A * float32)%type).

  Variable hypers : Perceptron.Hypers.

  Definition perceptron (r:Type) := 
    @extractible_main A B Params Perceptron.Hypers 
      (Perceptron.Learner n) hypers epochs _ (@list_Foldable (A*B)%type) r
      (fun T => ret T).
End PerceptronExtraction.

Extraction Language Haskell.
Extraction "hs/Perceptron.hs" perceptron.

Section KPerceptronExtraction.
  Variable n : nat. (*The dimensionality*)
  Variable m : nat. (*#examples*)
  Notation A := (Ak n m).
  Notation B := Bk.
  Variable d : A * B -> R.

  (*Variable m : nat. (*The number of training samples*)*)
  Variable epochs : nat.

  Notation Params := (KernelParams m)%type.

  Variable hypers : KernelPerceptron.Hypers.

  Notation Q := (A * B)%type.
  Definition kperceptron := 
    @extractible_main
      A B Params KernelPerceptron.Hypers
      (@KernelPerceptron.Learner n m (seq.seq Q) (list_Foldable Q))
      hypers
      epochs
      (seq.seq Q)
      (list_Foldable Q)
      (seq.seq Q)
      (fun T => ret T).
End KPerceptronExtraction.

Extraction Language Haskell.
Extraction "hs/KPerceptron.hs" kperceptron.