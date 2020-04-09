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
  
  Definition Akb: Type := float32_arr n. (*examples*)
  Definition Bkb := bool. (*labels*)

  Definition bsupport_vector: Type := Akb * Bkb.
  Definition bsupport_vectors: Type := AxVec sv (float32 * (bsupport_vector)).
  Context `{Foldable bsupport_vectors (float32 * bsupport_vector)}.
  
  Section predict.
    Open Scope f32_scope.

    Definition kernel_predict_budget
               (w: bsupport_vectors)
               (x: Akb) : Bkb :=
      foldable_foldM
        (fun wi_xi r =>
           let: (wi, (xi, yi)) := wi_xi in 
           r + (float32_of_bool yi) * wi * (K xi x))
        0 w > 0.
  End predict.
End KernelClassifierBudget.

Section KernelClassifierDes.
  Variable n : nat. (*the dimensionality*)
  Variable m : nat. (*#examples*)
  
  Variable des : nat. (*#support vectors*)
  Variable K: float32_arr n -> float32_arr n -> float32.
  
  Definition Akd: Type := float32_arr n. (*examples*)
  Definition Bkd := bool. (*labels*)

  Definition dsupport_vector: Type := Akd * Bkd.
  Definition dsupport_vectors: Type := AxVec des dsupport_vector.
  Definition dparams: Type := float32 * dsupport_vectors.
  Context `{F:Foldable dparams dsupport_vector}.
  Context `{F':Foldable dsupport_vectors dsupport_vector}.
  
  Section predict.
    Open Scope f32_scope.

    Definition kernel_predict_des
               (aw: dparams)
               (x: Akd) : Bkd :=
      let (a, w) := aw in
      foldable_foldM
        (fun wi_xi r =>
           let: (xi, yi) := wi_xi in 
           r + (float32_of_bool yi) * (K xi x))
        0 w > 0.
  End predict.
End KernelClassifierDes.

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
    Notation A := (Akb n).
    Notation B := Bkb.
    Definition Params := bsupport_vectors n (S sv).
    Context `{F: Foldable Params (float32 * (A * B))}.   
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
    Definition existing (s : Params) (yj : A*B) : bool :=
      let: (j, y) := yj in
      foldable_foldM
        (fun wi_xi r =>
          let: (_, (x, l)) := wi_xi in
            (f32_arr_eq x j) || r)
        false s.
        
    Definition upd_weights (p: Params) (yj: A): Params :=
      AxVec_map
        (fun xi => 
          let: (wi, (x, li)) := xi in
          if f32_arr_eq x yj then (wi+1, (x, li))
          else xi)
        p.
      
    (*This function requires that the Params be initialized with (S sv) support vectors*)  
    Definition add_new (p: Params) (yj: A*B): Params :=
      AxVec_cons (1, yj) (AxVec_init p).
    
    Definition budget_update (p: Params) (yj: A*B): Params :=
      if existing p yj then upd_weights p yj.1
      else add_new p yj.
      
    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (p:Params) : Params :=
      let: (example, label) := example_label in 
      let: predicted_label := kernel_predict_budget K p example in
      if Bool.eqb predicted_label label then p
      else (U p example_label).

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict_budget n (S sv) K F)
        (kernel_update K).
  End Learner.
End KernelPerceptronBudget.

Module KernelPerceptronDes.
  Section Learner.
    Variable n : nat. (*the dimensionality*)
    Variable m : nat. (*#examples*)
    Variable des : nat. (*#support vectors - 1*)
    Notation A := (Akd n).
    Notation B := Bkd.
    Definition DSup := dsupport_vectors n (S des).
    
    Definition Params := (float32 * DSup)%type.
    Context `{F: Foldable Params (A * B)}.
    Context `{F': Foldable DSup (A * B)}.   
    Variable K : float32_arr n -> float32_arr n -> float32. 
    
    Record Hypers : Type := mkHypers { alpha : float32; }.

    Open Scope f32_scope.
    (*Definition f32_arr_eq (x y : float32_arr n) : bool :=
      f32_fold2 true
        (fun a b z => if (f32_eq a b) then z else false)
        x y.*)
    
    Definition des_update (ap: Params) (yj: A*B): Params :=      
      let (a, p) := ap in
      ((f32_add f32_1 a), (AxVec_cons yj) (AxVec_init p)).
      
    Definition kernel_update 
      (K : float32_arr n -> float32_arr n -> float32)
          (h:Hypers) (example_label:A*B) (ap:Params) : Params :=
      let: (example, label) := example_label in
      let: (a, p) := ap in 
      let: predicted_label := kernel_predict_des K ap example in
      if Bool.eqb predicted_label label then ap
      else if f32_eq a (alpha h) then ap
           else des_update ap example_label.

    Definition Learner : Learner.t A B Hypers Params :=
      Learner.mk
        (fun _ => @kernel_predict_des n (S des) K F')
        (@kernel_update K).
  End Learner.
End KernelPerceptronDes.

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
  Notation A := (float32_arr_finType n).
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
  
  Context `{F : Foldable (bsupport_vectors n (S sv)) (float32 * bsupport_vector)}.
  Variable U : bsupport_vectors n (S sv) -> A * B -> bsupport_vectors n (S sv).
  Definition KaccuracyBudget := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptronBudget.Learner n sv F K U) hypers).

  Lemma Kcard_Params_Budget_size : INR #|Params| =
    INR (((2 ^ 32) * ((2 ^ (n * 32)) * 2)) ^ (S (sv))).    
    
  Proof.
    unfold Params. unfold bsupport_vector. unfold Akb.
    rewrite (@AxVec_card_gen (2 ^ 32 * (2 ^ (n * 32) * 2)) (S sv)).
    - rewrite pow_INR. auto.
    - rewrite card_prod. rewrite float32_card.
    rewrite card_prod.
    rewrite float32_arr_card. rewrite card_bool. auto.
    Qed.
    
  Require Import Omega.
  Lemma Kcard_Params_Budget_helper : INR (((2 ^ 32) * ((2 ^ (n * 32)) * 2)) ^ (S (sv)))
  = INR 2^((32*(S sv) + ((1 + n * 32)*(S sv)))).
  Proof.
  assert (H: muln (Nat.pow 2 (muln n 32)) 2 = muln 2 (Nat.pow 2 (muln n 32))%coq_nat).
    { rewrite <- multE. omega. } 
  rewrite ->  H. 
  assert (J: muln 2 (Nat.pow 2 (muln n 32)) = Nat.pow 2 (1 + (muln n 32))).
    { rewrite Nat.pow_succ_r'. auto. }
  rewrite -> J.
  rewrite <- Nat.pow_add_r. rewrite <- Nat.pow_mul_r.
  rewrite pow_INR. rewrite Nat.mul_add_distr_r. auto.
  Qed.
  
  Lemma Kcard_Params_Budget : INR #| Params | = 
      INR 2^((32*(S sv) + ((1 + n * 32)*(S sv)))).
  Proof.
  rewrite Kcard_Params_Budget_size.
  rewrite Kcard_Params_Budget_helper.
  auto.
  Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 KaccuracyBudget p < 1)
    (mut_ind : forall p : Params, mutual_independence d (KaccuracyBudget p)).

  Lemma Kperceptron_bound_budget eps (eps_gt0 : 0 < eps) init : 
    @main A B Params KernelPerceptronBudget.Hypers 
      (@KernelPerceptronBudget.Learner n sv F K U)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    INR 2^((32*(S sv) + ((1 + n * 32)*(S sv)))) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params_Budget.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralizationBudget.

Section KernelPerceptronGeneralizationDes.
  Variable n : nat. (*The dimensionality*)
  Variable m : nat. (*#examples*)
  Variable des : nat.
  Notation A := (float32_arr_finType n).
  Notation B := bool_finType.
  Variable d : A * B -> R.
  Variable d_dist : big_sum (enum [finType of A * B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m_gt0 : (0 < m)%nat.

  Variable epochs : nat.

  Variable hypers : KernelPerceptronDes.Hypers.
  Variable K : float32_arr n -> float32_arr n -> float32.

  Notation dsupport_vector := [finType of A * B].
  Notation Params := [finType of float32_finType * 
    (AxVec_finType (S des) dsupport_vector)].
  
  Context `{F : Foldable (dsupport_vectors n (S des)) dsupport_vector}.
  Definition KaccuracyDes := 
    @accuracy01 A _ m Params (Learner.predict 
      (@KernelPerceptronDes.Learner n des F K) hypers).

  Lemma Kcard_Params_Des_size : INR #|Params| =
    INR (2 ^ 32 * ((2 ^ (n * 32)) * 2) ^ (S (des))).    
    
  Proof.
    unfold Params. rewrite card_prod. rewrite float32_card. unfold dsupport_vector. unfold Akb.
    rewrite (@AxVec_card_gen (2 ^ (n * 32) * 2) (S des)).
    -  auto. 
    - rewrite card_prod. 
    rewrite float32_arr_card. rewrite card_bool. auto.
    Qed.
    
  Require Import Omega.
  Lemma Kcard_Params_Des_helper : INR (2 ^ 32 * ((2 ^ (n * 32)) * 2) ^ (S (des)))
  = INR 2 ^ (32 + (1 + n * 32) * (S des)).
  Proof.
  assert (H: muln (Nat.pow 2 (muln n 32)) 2 = muln 2 (Nat.pow 2 (muln n 32))%coq_nat).
    { rewrite <- multE. omega. } 
  rewrite ->  H. 
  assert (J: muln 2 (Nat.pow 2 (muln n 32)) = Nat.pow 2 (1 + (muln n 32))).
    { rewrite Nat.pow_succ_r'. auto. }
  rewrite -> J.
  (*rewrite <- Nat.pow_add_r.*) rewrite <- Nat.pow_mul_r. rewrite <- Nat.pow_add_r.
  rewrite pow_INR. auto.
  Qed.
  
  Lemma Kcard_Params_Des : INR #| Params | = 
      INR 2 ^ (32 + (1 + n * 32) * (S des)).
  Proof.
  rewrite Kcard_Params_Des_size.
  rewrite Kcard_Params_Des_helper.
  auto.
  Qed.

  Variables 
    (not_perfectly_learnable : 
       forall p : Params, 0 < expVal d m_gt0 KaccuracyDes p < 1)
    (mut_ind : forall p : Params, mutual_independence d (KaccuracyDes p)).

  Lemma Kperceptron_bound_Des eps (eps_gt0 : 0 < eps) init : 
    @main A B Params KernelPerceptronDes.Hypers 
      (@KernelPerceptronDes.Learner n des F K)
      hypers m m_gt0 epochs d eps init (fun _ => 1) <=
    INR 2 ^ (32 + (1 + n * 32) * (S des)) * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite -Kcard_Params_Des.
    apply: Rle_trans; first by apply: main_bound.
    apply: Rle_refl.
  Qed.
End KernelPerceptronGeneralizationDes.

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
  Notation A := (Akb n).
  Notation B := Bkb.
  Variable d : A * B -> R.

  (*Variable m : nat. (*The number of training samples*)*)
  Variable epochs : nat.

  Notation Params := (KernelPerceptronBudget.Params n sv)%type.

  Variable hypers : KernelPerceptronBudget.Hypers.
  Variable K : float32_arr n -> float32_arr n -> float32.

  Notation Q := (A * B)%type.
  Variable U : (@KernelPerceptronBudget.Params n sv) -> 
     Q -> (@KernelPerceptronBudget.Params n sv).
  
  Context `{F : Foldable Params (float32 * bsupport_vector n)}.
  Definition kperceptronbudget (r:Type) := 
    @extractible_main
      A B Params KernelPerceptronBudget.Hypers
      (@KernelPerceptronBudget.Learner n sv F K U)
      hypers
      epochs
      (seq.seq Q)
      (list_Foldable Q)
      r
      (fun T => ret T).
End KPerceptronExtractionBudget.

Extraction Language Haskell.
Extraction "hs/KPerceptronBudget.hs" kperceptronbudget linear_kernel quadratic_kernel KernelPerceptronBudget.budget_update.