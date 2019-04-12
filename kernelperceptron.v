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

  Definition Akb := ('I_m * float32_arr n)%type. (*examples*)
  Definition Bkb := bool. (*labels*)
  Context {support_vectors} `{Foldable support_vectors ('I_sv * float32_arr n * bool)}.
  Definition KernelParamsBudget := (float32 *support_vectors * float32_arr sv)%type.

  Section predict.
    Open Scope f32_scope.

    Definition kernel_predict_budget (K : float32_arr n -> float32_arr n -> float32) 
        (w : KernelParamsBudget) (x : Akb) : Bkb :=
      let (u, T) := w.1 in 
      foldable_foldM
        (fun xi_yi r =>
           let: ((i, xi), yi) := xi_yi in
           let: (j, xj) := x in 
           let: wi := f32_get i w.2 in 
           r + (float32_of_bool yi) * wi * (K xi xj))
        0 T > 0.
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
    Variable sv : nat. (*#support vectors*)
    Notation A := (Ak n m).
    Notation B := Bk.
    Context {support_vectors} `{F:Foldable support_vectors ('I_sv * float32_arr n * B)}.        
    Definition Params := @KernelParamsBudget sv support_vectors.
    Variable K : float32_arr n -> float32_arr n -> float32.
    Variable U : Params -> float32_arr n -> Params. 
    
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
    
    (*Definition of existing that doesn't work*)
    (*Definition existing (s : support_vectors) (e : float32_arr n) : nat :=
      foldable_foldM
        (fun x r =>
          let: ((i, xi), l) := x in
          let: y := f32_arr_eq xi e in
          if y then i else r)
          (S sv) s.*)
    
    Definition existing (s : support_vectors) (e : float32_arr n) : nat :=
       O.
       
    Definition upd_weights  
      (w : float32_arr sv) (s t : float32) : float32_arr sv :=       
      if f32_eq t f32_0
        then f32_upd_f32 s f32_0 w
        else f32_upd_f32 s (f32_get_f32 s w + 1) w.
      
    (*Definition of replace that doesn't work *)
    (*Definition replace (s : support_vectors) (e : float32_arr n)
        (t : float32) : support_vectors :=
    foldable_mapM 
      (fun x => 
        let: ((i, x'),y) := x in
        if f32_eq (nat_to_f32 i) t 
          then ((i, e),y)
          else ((i, x'),y))
       s.*)
    
    Definition replace (s : support_vectors) (e : float32_arr n)
        (t : float32) : support_vectors := s.
    
    Definition index_update (i : float32) : float32 :=
      if f32_eq (i + f32_1) (nat_to_f32 sv) 
        then f32_0 else i + f32_1. 
   
    Definition budget_update (p : Params) (e : float32_arr n) : Params :=
      let: (supports_index, weights) := p in
      let: (index, supports) := supports_index in
      let: t := existing supports e in
      if t < (S sv) 
        then (* increment existing support vector's weight*)
        ((index,supports), upd_weights weights (nat_to_f32 t) f32_1)
        else (* replace support vector at index with e*)
        ((index_update index, replace supports e index), 
           upd_weights weights index f32_0).
      
    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: ((i, example), label) := example_label in 
      let: predicted_label := kernel_predict_budget K p (i, example) in
      if Bool.eqb predicted_label label then p
      else (budget_update p example).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict_budget n m sv support_vectors F K)
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

  (*Represent the training set as a one-dimensional (flattened) float array.*)
  Definition support_vectors_budget := float32_arr_finType (sv*n).
  Context {H: Foldable support_vectors_budget ('I_sv * float32_arr n * B)}.

  Notation Params := [finType of {:float32_finType * support_vectors_budget * float32_arr_finType sv}].
  Variable U : Params -> float32_arr n -> Params.
  Definition KaccuracyBudget := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptronBudget.Learner n m sv support_vectors_budget H K U) hypers).

  Lemma Kcard_Params_Budget : INR #|Params| = 2 ^ ((32) + (sv*n*32) + (sv*32)).
  Proof.
    rewrite card_prod !float32_arr_card.
    rewrite /training_set card_prod !float32_arr_card.
    rewrite float32_card.
    rewrite mult_INR !pow_INR.
    rewrite mult_INR !pow_INR.
    rewrite pow_add.
    rewrite pow_add.
    reflexivity.
    (*rewrite mult_INR !pow_INR /= pow_add //.*)
  Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 KaccuracyBudget p < 1)
    (mut_ind : forall p : Params, mutual_independence d (KaccuracyBudget p)).

  Lemma Kperceptron_bound_budget eps (eps_gt0 : 0 < eps) init : 
    @main A B Params KernelPerceptronBudget.Hypers 
      (@KernelPerceptronBudget.Learner n m sv support_vectors_budget H K U)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    2^((32) + (sv*n*32) + (sv*32)) * exp (-2%R * eps^2 * mR m).
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