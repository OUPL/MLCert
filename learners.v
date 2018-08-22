Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist OUVerT.dyadic.

Require Import MLCert.monads MLCert.noise MLCert.samplers.

Module Learner.
  Record t (X Y Hypers Params : Type) :=
    mk { predict : Hypers -> Params -> X -> Y;
         update : Hypers -> X*Y -> Params -> Params }.
End Learner.

Section extractible_semantics.
  Variable X Y Params Hypers : Type.
  Variable learner : Learner.t X Y Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable epochs : nat.
  Context {training_set} `{Foldable training_set (X*Y)}.

  Variable r : Type.
  Notation C t := (Cont r t).

  Variable noise_model : training_set -> C training_set.

  Variable sample : (X*Y -> R) -> C training_set.

  Definition noised_sample (d:X*Y->R) : C training_set := 
    T <-- sample d;
    noise_model T.

  Definition learn_func (init:Params) (T:training_set) : Params := 
    foldrM (fun epoch p_epoch =>
      foldable_foldM (M:=Id) (fun xy p =>
        ret (Learner.update learner h xy p))
        p_epoch T)
      init (enum 'I_epochs).

  Definition learn (init:Params) (T:training_set) : C Params :=
    fun f => f (learn_func init T).

  Definition extractible_main (d:X*Y->R) (init:Params)
    : C (Params * training_set) :=
    T <-- noised_sample d;
    p <-- learn init T;
    ret (p, T).
End extractible_semantics.

Section rv_impulse_extractible_semantics.
  Variable X Y Params Hypers : Type.
  Variable x : Type.
  Variable x_of_nat : nat -> x.
  Variable example_mapM : forall (M:Type->Type), (x -> M x) -> X -> M X.  
  Variable learner : Learner.t X Y Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable epochs : nat.

  Context {training_set} `{Foldable training_set (X*Y)}.
  Context {sampler_state} `{BasicSamplers sampler_state}.      

  Variable r : Type.  
  Notation C t := (Cont r t).
  
  Variable sample : (X*Y -> R) -> C training_set.

  Definition rv_impulse_noise_model (p:D) (t:training_set) : C training_set :=
    Ts <-- rv_impulse example_mapM x_of_nat p t init_sampler_state;
    let: (T,s) := Ts in 
    ret T.
  
  Definition rv_impulse_extractible_main (d:X*Y->R) (p:D) (init:Params)
    : C (Params * training_set) :=
    extractible_main learner h epochs (rv_impulse_noise_model p) sample d init.
End rv_impulse_extractible_semantics.      

Section training_set.
  Variable m : nat.
  Definition semantic_training_set (X Y:finType) := training_set X Y m.
  Variables X Y : finType.

  Definition semantic_training_set_foldrM M `(Monad M) (R:Type)
             (f:X*Y -> R -> M R) (r:R) (t:semantic_training_set X Y) : M R
    := foldrM (fun i r => f (t i) r) r (enum 'I_m).
         
  Definition semantic_training_set_mapM M `(Monad M)
             (f:X*Y -> M (X*Y)%type) (t:semantic_training_set X Y)
    : M (semantic_training_set X Y)
    := foldrM
         (fun i (r:semantic_training_set X Y) =>
            xy' <-- f (t i);
            ret (finfun (fun j => if i==j then xy' else r j)))
         t (enum 'I_m).

  Global Instance semantic_TrainingSet
    : Foldable (semantic_training_set X Y) (X*Y) :=
    mkFoldable semantic_training_set_foldrM semantic_training_set_mapM.
End training_set.             

Section semantics.
  Variables X Y Params : finType. 
  Variable Hypers : Type.
  Variable learner : Learner.t X Y Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.
  Variable epochs : nat.
  Notation C := (@Cont R).

  Definition semantic_sample (d:X*Y -> R) : C (training_set X Y m) :=
    fun f => big_sum (enum (training_set X Y m)) (fun T => 
      (prodR (fun _:'I_m => d)) T * f T).

  Definition observe (t:Type) (p:pred t) : t -> C t :=
    fun t f => if p t then f t else 0.

  Definition accuracy := accuracy01 (m:=m) (Learner.predict learner h).

  Definition post (d:X*Y -> R) (eps:R) 
      (pT : Params * training_set X Y m) : bool :=
    let: (p, T) := pT in 
    Rlt_le_dec (expVal d m_gt0 accuracy p + eps) (empVal accuracy T p).
  
  Definition semantic_main (d:X*Y -> R) (init:Params) := 
    extractible_main learner h epochs (fun T => ret T) semantic_sample d init.

  Definition main (d:X*Y -> R) (eps:R) (init:Params) 
    : C (Params * training_set X Y m) :=
    pT <-- semantic_main d init;
    let: (p,T) := pT in
    observe (post d eps) (p,T).

  Variables
    (d:X*Y -> R) 
    (d_dist : big_sum (enum [finType of X*Y]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : Params, mutual_independence d (accuracy p))
    (not_perfectly_learnable : 
      forall p : Params, 0 < expVal d m_gt0 accuracy p < 1).

  Lemma main_bound (eps:R) (eps_gt0 : 0 < eps) (init:Params) :
    main d eps init (fun _ => 1) <= 
    INR #|Params| * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite /main/semantic_main/extractible_main/bind/=/Cbind/Cret.
    rewrite /noised_sample/Cbind/=/Cbind/semantic_sample.
    rewrite big_sum_pred2; apply: Rle_trans; last first.
    { apply chernoff_bound_accuracy01 
        with (d:=d) (learn:=fun t => learn_func learner h epochs init t) => //.
      { move => p; apply: mut_ind. }
      move => p; apply: not_perfectly_learnable. }
    rewrite /probOfR/=. 
    apply big_sum_le => c; rewrite /in_mem Rmult_1_r /= => _; apply: Rle_refl.
  Qed.
End semantics.

Section OracleLearner.
  Variables X Y Hypers Params : Type.
  Variable oracular_params : Params.
  Variable predict : Hypers -> Params -> X -> Y.
  
  Definition OracleLearner : Learner.t X Y Hypers Params :=
    Learner.mk predict (fun _ _ _ => oracular_params).
End OracleLearner.

Section oracular_semantics.
  Variables X Y Params : finType. 
  Variable Hypers : Type.
  Variable learner : Learner.t X Y Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.
  Notation C := (@Cont R).

  Variable oracle : training_set X Y m -> Params.

  Notation semantic_sample m := (@semantic_sample X Y m).
  Notation accuracy := (@accuracy X Y Params Hypers learner h m).
  Notation post := (@post X Y Params Hypers learner h m m_gt0).
  
  Definition oracular_main (d:X*Y -> R) (eps:R) (init:Params) 
    : C (Params * training_set X Y m) :=
    T <-- semantic_sample m d;
    p <-- ret (oracle T);
    observe (post d eps) (p,T).

  Variables
    (d:X*Y -> R) 
    (d_dist : big_sum (enum [finType of X*Y]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : Params, mutual_independence d (accuracy p))
    (not_perfectly_learnable : 
      forall p : Params, 0 < expVal d m_gt0 accuracy p < 1).

  Lemma oracular_main_bound (eps:R) (eps_gt0 : 0 < eps) (init:Params) :
    oracular_main d eps init (fun _ => 1) <= 
    INR #|Params| * exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite /oracular_main/bind/=/Cbind/Cret.
    rewrite /(semantic_sample m)/Cbind/=/Cbind.
    rewrite big_sum_pred2; apply: Rle_trans; last first.
    { apply chernoff_bound_accuracy01 
        with (d:=d) (learn:=fun t => oracle t) => //.
      { move => p; apply: mut_ind. }
      move => p; apply: not_perfectly_learnable. }
    rewrite /probOfR/=. 
    apply big_sum_le => c; rewrite /in_mem Rmult_1_r /= => _; apply: Rle_refl.
  Qed.
End oracular_semantics.

Section oracular_holdout_semantics.
  Variables X Y Params : finType. 
  Variable Hypers : Type.
  Variable learner : Learner.t X Y Hypers Params.
  Variable h : Hypers.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.
  Notation C := (@Cont R).

  Variable oracle : training_set X Y m -> Params.

  Notation semantic_sample m := (@semantic_sample X Y m).
  Notation accuracy := (@accuracy X Y Params Hypers learner h m).
  Notation post := (@post X Y Params Hypers learner h m m_gt0).

  Definition eps_hyp_ok (d:X*Y -> R) (eps:R) (t:training_set X Y m) : bool :=
    Rlt_le_dec eps 
      (1 - (expVal (A:=X) (B:=Y) d m_gt0 (Hyp:=Params)
                  (accuracy01 (A:=X) (B:=Y) (Params:=Params) (Learner.predict learner h)) (oracle t))).      
    
  Definition oracular_holdout_main (d:X*Y -> R) (eps:R) (init:Params) 
    : C (Params * training_set X Y m) :=
    T_train <-- semantic_sample m d;
    _ <-- observe (eps_hyp_ok d eps) T_train;            
    p <-- ret (oracle T_train);
    T_test <-- semantic_sample m d;
    observe (post d eps) (p,T_test).

  Variables
    (d:X*Y -> R) 
    (d_dist : big_sum (enum [finType of X*Y]) d = 1)
    (d_nonneg : forall x, 0 <= d x) 
    (mut_ind : forall p : Params, mutual_independence d (accuracy p))
    (not_perfectly_learnable : 
      forall p : Params, 0 < expVal d m_gt0 accuracy p < 1).

  Lemma oracular_holdout_main_bound (eps:R) (eps_gt0 : 0 < eps) (init:Params) :
    oracular_holdout_main d eps init (fun _ => 1) <= 
    exp (-2%R * eps^2 * mR m).
  Proof.
    rewrite /oracular_holdout_main/bind/=/Cbind/Cret.
    rewrite /(semantic_sample m)/Cbind/=/Cbind.
    have H:
      big_sum (enum {ffun 'I_m -> X * Y})
       (fun T : {ffun 'I_m -> X * Y} =>
          exp (- (2) * (eps * (eps * 1)) * mR m) *
          prodR (T:=prod_finType X Y) (fun _ : 'I_m => d) T) =
      exp (- (2) * (eps * (eps * 1)) * mR m).
    { by rewrite big_sum_scalar prodR_dist => //; rewrite Rmult_1_r. }
    rewrite -H; apply: big_sum_le => T_train Htrain.
    rewrite [exp _ * _]Rmult_comm; apply: Rmult_le_compat_l; first by apply: prodR_nonneg.
    rewrite /observe; case Heps: (eps_hyp_ok _ _); last by apply: Rlt_le; apply: exp_pos.
    apply: Rle_trans; last first.
    { apply: (@chernoff_bound_accuracy01_holdout
                _ _ _ d_dist d_nonneg _ _ _ _ mut_ind not_perfectly_learnable
                (oracle T_train) eps) => //.
      move: Heps; rewrite /eps_hyp_ok; case: (Rlt_le_dec _ _) => // Hlt. }
    rewrite /probOfR big_sum_pred2; apply: big_sum_le => T_test Htest.
    by rewrite Rmult_1_r; apply: Rle_refl.
  Qed.                                                 
End oracular_holdout_semantics.
