Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import NArith.
Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.float32 MLCert.learners MLCert.extraction_hs MLCert.monads.

Section KernelClassifier.
  Variable n : nat. (*the dimensionality*)
  Variable m : nat. (*#examples*)
  
  Variable sv : nat. (*#support vectors*)

  Definition Ak := ('I_m * float32_arr n)%type. (*examples*)
  Definition Bk := bool. (*labels*)
  (*Context {support_vectors} `{Foldable support_vectors (Ak * Bk)}.*)
  Context {support_vectors} `{Foldable support_vectors ('I_sv * float32_arr n * bool)}.
  Definition KernelParams := (support_vectors * float32_arr sv)%type.

  Section predict.
    Open Scope f32_scope.
    Definition linear_kernel {n} (x y : float32_arr n) : float32 :=
      f32_dot x y.
    Definition quadratic_kernel (x y : float32_arr n) : float32 :=
      (f32_dot x y) ** 2.

    Definition kernel_predict (K : float32_arr n -> float32_arr n -> float32) 
        (w : KernelParams) (x : Ak) : Bk :=
      let T := w.1 in 
      foldable_foldM
        (fun xi_yi r =>
           let: ((i, xi), yi) := xi_yi in
           let: (j, xj) := x in 
           let: wi := f32_get i w.2 in 
           r + (float32_of_bool yi) * wi * (K xi xj))
        0 T > 0.
  End predict.
End KernelClassifier.

Module KernelPerceptron.
  Section Learner.
    Variable n : nat. (*the dimensionality*)
    Variable m : nat. (*#examples*)
    Variable sv : nat. (*#support vectors*)
    Notation A := (Ak n m).
    Notation B := Bk.
    Context {support_vectors} `{F:Foldable support_vectors (A * B)}.        
    Definition Params := @KernelParams m support_vectors.
    Variable K : float32_arr n -> float32_arr n -> float32.
    

    Record Hypers : Type := mkHypers { }.

    Open Scope f32_scope.

    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: ((i, example), label) := example_label in 
      let: predicted_label := kernel_predict K p (i, example) in
      if Bool.eqb predicted_label label then p
      else (p.1, f32_upd i (f32_get i p.2 + 1) p.2).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict n m _ support_vectors F K)
        (kernel_update K).
  End Learner.
End KernelPerceptron.

Module KernelPerceptronBudget.
  Section Learner.
    Variable n : nat. (*the dimensionality*)
    Variable m : nat. (*#examples*)
    Variable sv : nat. (*#support vectors*)
    Notation A := (Ak n m).
    Notation B := Bk.
    Context {support_vectors} `{F:Foldable support_vectors (A * B)}.        
    Definition Params := @KernelParams m support_vectors.
    Variable K : float32_arr n -> float32_arr n -> float32.
    

    Record Hypers : Type := mkHypers { }.

    Open Scope f32_scope.

    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: ((i, example), label) := example_label in 
      let: predicted_label := kernel_predict K p (i, example) in
      if Bool.eqb predicted_label label then p
      else (p.1, f32_upd i (f32_get i p.2 + 1) p.2).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict n m _ support_vectors F K)
        (kernel_update K).
  End Learner.
End KernelPerceptronBudget.

Require Import Reals Fourier.
Require Import OUVerT.bigops OUVerT.dist OUVerT.chernoff OUVerT.learning.

Section KernelPerceptronGeneralization.
  Variable n : nat. (*The dimensionality*)
  Variable m : nat. (*#examples*)
  Variable sv : nat.
  Notation A := [finType of 'I_m * float32_arr_finType n].
  Notation B := bool_finType.
  Variable d : A * B -> R.
  Variable d_dist : big_sum (enum [finType of A * B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m_gt0 : (0 < m)%nat.

  Variable epochs : nat.

  Variable hypers : KernelPerceptron.Hypers.
  Variable K : float32_arr n -> float32_arr n -> float32.

  (*Represent the training set as a one-dimensional (flattened) float array.*)
  Definition support_vectors := float32_arr_finType (m*n).
  Context {H: Foldable support_vectors (A * B)}.

  Notation Params := [finType of {:support_vectors * float32_arr_finType m}].
  Definition Kaccuracy := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptron.Learner n m support_vectors H K) hypers).

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
      (@KernelPerceptron.Learner n m support_vectors H K)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    2^(m*n*32 + m*32) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralization.

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
  Variable K : float32_arr n -> float32_arr n -> float32.

  Notation Q := (A * B)%type.
  Definition kperceptron (r:Type) := 
    @extractible_main
      A B Params KernelPerceptron.Hypers
      (@KernelPerceptron.Learner n m (seq.seq Q) (list_Foldable Q) K)
      hypers
      epochs
      (seq.seq Q)
      (list_Foldable Q)
      r
      (fun T => ret T).
End KPerceptronExtraction.

Extraction Language Haskell.
Extraction "hs/KPerceptron.hs" kperceptron linear_kernel quadratic_kernel.