Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.float32.

Section LinearClassifier.
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
End LinearClassifier.

Module Learner.
  Record t (A B hypers params : Type) :=
    mk { predict : hypers -> params -> A -> B;
         update : hypers -> A*B -> params -> params }.
End Learner.

Section learning.
  Variables A B hypers params : Type.
  Variable learner : Learner.t A B hypers params.
  Variable h : hypers.

  Fixpoint learn (p:params) (training_set:list (A*B)) : params :=
    match training_set with
    | [] => p
    | ab :: training_set' => learn (Learner.update learner h ab p) training_set'
    end.
End learning.

Module Perceptron.
  Section Learner.
    Variable n : nat.     
    Notation A := (A n).
    Notation B := B.
    Notation Params := (Params n).

    Record Hypers : Type :=
      mkHypers { alpha : float32 }.

    Open Scope f32_scope.    
    
    Definition update (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: (example, label) := example_label in
      let: predicted_label := predict p example in
      if Bool.eqb predicted_label label then p
      else let: (w, b) := p in
           (f32_map2 (fun x1 x2 => x1 + (alpha h)*label*x2) w example, b+label).
    
    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @predict n)
        update.
  End Learner.
End Perceptron.

Module PerceptronExtractionTest.
  Local Open Scope f32_scope.
  Definition n := 2.
  Definition alpha : Perceptron.Hypers := Perceptron.mkHypers 1.
  Definition training_set ex1 ex2 : list (A n*B) := [(ex1,true); (ex2,false)].
  Definition go init_weights ex1 ex2 :=
    @learn
      _ _ _ _
      (Perceptron.Learner n) alpha (init_weights, 0) (training_set ex1 ex2).
  Extraction Language Haskell.
  Extraction "Perceptron.hs" go.
End PerceptronExtractionTest.

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

  Variable h : Perceptron.Hypers.

  (*J is 0-1 loss applied to Perceptron's prediction function*)
  Notation Params := [finType of A * float32_finType].
  Definition J := @loss01 A _ m Params (Learner.predict (Perceptron.Learner n) h).

  Lemma card_Params : INR #|Params| = 2^(n*32 + 32).
  Proof. by rewrite pow_add card_prod mult_INR float32_card float32_arr_card !pow_INR. Qed.
    
  Lemma chernoff_bound_loss01_perceptron
      (eps : R) (eps_gt0 : 0 < eps)
      (not_perfectly_learnable : forall p : Params, 0 < expErr d m_gt0 J p < 1)
      (ind : forall p : Params, mutual_independence d (J p)) :
    probOfR (prodR (fun _ : 'I_m => d))
          [pred T:training_set A B m
          | [exists i : 'I_#|eps_Hyp d m_gt0 J eps|,
             let: h := projT1 (enum_val i)
             in Rle_lt_dec eps (Rabs (expErr d m_gt0 J h - empErr J T h))]]
    <= 2 * 2^(n*32 + 32) * exp (-2%R * eps^2 * mR m).
  Proof. by rewrite -card_Params; apply: chernoff_bound_loss01. Qed.
End PerceptronGeneralization.
