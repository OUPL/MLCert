Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import NArith.
Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.axioms MLCert.float32 MLCert.learners MLCert.extraction_hs MLCert.monads.

Section KernelClassifier.
  Variable n : nat. (*the dimensionality*)
  Variable m : nat. (*#examples*)

  Definition Ak := ('I_m * float32_arr n)%type. (*examples*)
  Definition Bk := bool. (*labels*)
  Context {support_vectors} `{Foldable support_vectors ('I_m * float32_arr n * bool)}.
  Definition KernelParams := (support_vectors * float32_arr m)%type.

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

Section KernelClassifierBudget.
  Variable n : nat. (*the dimensionality*)
  Variable m : nat. (*#examples*)
  
  Variable sv : nat. (*#support vectors*)
  Variable K: float32_arr n -> float32_arr n -> float32.
  
  Definition Akb: Type := ('I_m * float32_arr n). (*examples*)
  Definition Bkb := bool. (*labels*)

  Definition bsupport_vector: Type := Akb * Bkb.
  Definition bsupport_vectors: Type := AxVec sv (float32 * bsupport_vector).
  Context `{Foldable bsupport_vectors (float32 * bsupport_vector)}.
  
  Section predict.
    Open Scope f32_scope.

    Definition kernel_predict_budget
               (w: bsupport_vectors)
               (x: Akb) : Bkb :=
      foldable_foldM
        (fun wi_xi r =>
           let: (_, x) := x in
           let: (wi, ((_, xi), yi)) := wi_xi in 
           r + (float32_of_bool yi) * wi * (K xi x))
        0 w > 0.
  End predict.
End KernelClassifierBudget.

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
        (fun _ => @kernel_predict n m support_vectors F K)
        (kernel_update K).
  End Learner.
End KernelPerceptron.

Module KernelPerceptronBudget.
  Section Learner.
    Variable n : nat. (*the dimensionality*)
    Variable m : nat. (*#examples*)
    Variable sv : nat. (*#support vectors - 1*)
    Notation A := (Ak n m).
    Notation B := Bk.
    Definition Params := bsupport_vectors n m (S sv).
    Context `{F: Foldable (bsupport_vectors n m (S sv)) (float32 * bsupport_vector n m)}.   
    Variable K : float32_arr n -> float32_arr n -> float32.
    Variable U : Params -> A*B -> Params. 
    
    Record Hypers : Type := mkHypers { }.

    Open Scope f32_scope.
    Definition f32_arr_eq (x y : float32_arr n) : bool :=
      f32_fold2 true
        (fun a b z => if (f32_eq a b) then z else false)
        x y.
        
    Fixpoint nat_to_f32 (x : nat) : float32 :=
      match x with
      | O => f32_0
      | S x' => (nat_to_f32 x') + f32_1
      end.

    (*Is x in s?*)
    Set Printing All.
    Definition existing (s : Params) (yj : A) : bool :=
      let: (j, y) := yj in 
      foldable_foldM
        (fun wi_xi r =>
           let: (_, ((i, x), l)) := wi_xi
           in (i == j) || r)
        false s.
       
    Definition upd_weights (p: Params) (yj: A): Params :=
      let: (j, y) := yj in 
      AxVec_map
        (fun xi =>
           let: (wi, ((i, x), li)) := xi in 
           if i == j then (wi+1, ((i, x), li))
           else xi)
        p.

    Definition add_new (p: Params) (yj: A*B): Params :=
      AxVec_cons (1, yj) (AxVec_tail p).
    
    Definition budget_update (p: Params) (yj: A*B): Params :=
      if existing p yj.1 then upd_weights p yj.1
      else add_new p yj.
      
    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: ((i, example), label) := example_label in 
      let: predicted_label := kernel_predict_budget K p (i, example) in
      if Bool.eqb predicted_label label then p
      else (U p example_label).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict_budget n m (S sv) K F)
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
  Definition KPsupport_vectors := float32_arr_finType (m*n).
  Context {H: Foldable KPsupport_vectors (A * B)}.
  
  Notation Params := [finType of {:KPsupport_vectors * float32_arr_finType m}].
  Definition Kaccuracy := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptron.Learner n m KPsupport_vectors H K) hypers).

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
      (@KernelPerceptron.Learner n m KPsupport_vectors H K)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    2^(m*n*32 + m*32) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralization.

Section KernelPerceptronGeneralizationBudget.
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

  Variable hypers : KernelPerceptronBudget.Hypers.
  Variable K : float32_arr n -> float32_arr n -> float32.

  Notation bsupport_vector := [finType of A * B].
  Notation Params := (AxVec_finType (S sv) [finType of (float32_finType * bsupport_vector)]).
  
  Context `{F : Foldable (bsupport_vectors n m (S sv)) (float32 * bsupport_vector)}.
  Variable U : bsupport_vectors n m (S sv) -> A * B -> bsupport_vectors n m (S sv).
  Definition KaccuracyBudget := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptronBudget.Learner n m sv F K U) hypers).

(*Lemma fun_thing : INR #| AxVec_finType sv [finType of 'I_m]| = 2 ^ (sv * m).
  rewrite (@AxVec_card sv m).
  - rewrite pow_INR. reflexivity.
  - rewrite card_ord. Check AxVec_card_gen. Admitted.*)
  Lemma Kcard_Params_Budget : INR #|Params| = (*2 ^ ((32) + (sv*n*32) + (sv*32))*)
    INR ((2 ^ 32) * (m * (2 ^ (n * 32)) * 2)) ^ (S (sv)).
    
  Proof.
    unfold Params. unfold bsupport_vector. unfold Akb.
    rewrite (@AxVec_card_gen (2 ^ 32 * (m * 2 ^ (n * 32) * 2)) (S sv)).
    - rewrite pow_INR. auto.
    - rewrite card_prod. rewrite float32_card.
    rewrite card_prod. rewrite card_prod. rewrite card_ord.
    rewrite float32_arr_card. rewrite card_bool. auto.
    Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 KaccuracyBudget p < 1)
    (mut_ind : forall p : Params, mutual_independence d (KaccuracyBudget p)).

  Lemma Kperceptron_bound_budget eps (eps_gt0 : 0 < eps) init : 
    @main A B Params KernelPerceptronBudget.Hypers 
      (@KernelPerceptronBudget.Learner n m sv F K U)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    INR ((2 ^ 32) * (m * (2 ^ (n * 32)) * 2)) ^ (S (sv)) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params_Budget.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralizationBudget.

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

Section KPerceptronExtractionBudget.
  Variable n : nat. (*The dimensionality*)
  Variable m : nat. (*#examples*)
  Variable sv : nat.
  Notation A := (Ak n m).
  Notation B := Bk.
  Variable d : A * B -> R.

  (*Variable m : nat. (*The number of training samples*)*)
  Variable epochs : nat.

  Notation Params := (KernelPerceptronBudget.Params n m sv)%type.

  Variable hypers : KernelPerceptronBudget.Hypers.
  Variable K : float32_arr n -> float32_arr n -> float32.

  Notation Q := (A * B)%type.
  Notation Q' := ('I_m * float32_arr n * B)%type.
  Variable U : (@KernelPerceptronBudget.Params n m sv) -> 
     Q -> (@KernelPerceptronBudget.Params n m sv).
  
  Context `{F : Foldable Params (float32 * bsupport_vector n m)}.
  Definition kperceptronbudget (r:Type) := 
    @extractible_main
      A B Params KernelPerceptronBudget.Hypers
      (@KernelPerceptronBudget.Learner n m sv F K U)
      hypers
      epochs
      (seq.seq Q')
      (list_Foldable Q')
      r
      (fun T => ret T).
End KPerceptronExtractionBudget.

Extraction Language Haskell.
Extraction "hs/KPerceptronBudget.hs" kperceptronbudget linear_kernel quadratic_kernel KernelPerceptronBudget.budget_update.