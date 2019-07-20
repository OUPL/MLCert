(**Require Import MLCert.axioms.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations.
Require Import ZArith.
Require Import MLCert.float32.
Require Import MLCert.extraction_ocaml.
Require Import Coq.Logic.FunctionalExtensionality.
**)
Require Import MLCert.extraction_ocaml.
Require Import List. Import ListNotations.
Require Import QArith.
Require Import OUVerT.extrema.
Require Import OUVerT.banach.
Require Import OUVerT.orderedtypes.

(**Require Import FunctionalExtensionality.**)

(**Open Scope f32_scope.**)


Require Import OUVerT.numerics.
Require Import OUVerT.generalized_bigops.
Require Import OUVerT.dyadic.
Require Import ProofIrrelevance.

Require Import OUVerT.compile.
Require Import Reals.SeqProp.
Require Import Reals.Rseries.
Require Import Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.Rpower.
Import OUVerT.numerics.Numerics.
Import OUVerT.extrema.num_Extrema.

Require Import mathcomp.algebra.matrix.
Require Import Reals.Rcomplete.

Require Import Psatz.


From mathcomp Require Import all_ssreflect.



Lemma total_order_max: forall (T : Type) (P : T->T->Prop),
   (forall (t1 t2 t3 : T), P t1 t2 -> P t2 t3 -> P t1 t3) ->
   (forall (t1 t2 : T), P t1 t2 \/ P t2 t1) ->
   (forall (t : T), P t t) ->
   (forall (t1 t2 : T), {t1 = t2} + {t1 <> t2})->
   (forall (l : list T), length l <> O ->
      exists t1 : T, (forall t2 : T, In t2 l -> P t1 t2)).
Proof.
  intros.
  induction l.
  { exfalso. apply H2. auto. }
  destruct l.
  { 
    exists a.
    intros.
    inversion H3.
    { rewrite H4; auto. }
    inversion H4.
  }
  destruct IHl.
  { simpl. unfold not. intros. inversion H3. }
  destruct H0 with x a.
  {
    exists x.
    intros.
    destruct X with a t2.
    { rewrite <- e; auto. }
    inversion H5.
    { rewrite H6 in n. exfalso; apply n; auto. }
    apply H3; auto.
  }
  exists a.
  intros.
  destruct X with a t2.
  { rewrite e; auto. }
  apply H with x; auto.
  apply H3.
  inversion H5; auto.
  exfalso. apply n; auto.
Qed.

Lemma in_iff: forall (T : Type) (l : list T) (a : T), SetoidList.InA (fun x y : T => x = y) a l <-> In a l.
Proof.
  intros.
  split; intros.
  {    
    induction l.
      inversion H.
    inversion H.
    {
      rewrite H1.
      constructor.
      auto.
    }
    constructor 2.
    apply IHl.
    auto.
  }
  induction l; inversion H.
  {
    rewrite H0.
    constructor.
    auto.
  }
  constructor 2.
  apply IHl.
  auto.
Qed.
  

Lemma no_dup_iff: forall (T : Type) (l : list T), SetoidList.NoDupA (fun x y : T => x = y) l <-> NoDup l.
Proof.
  intros.
  split.
  {
    intros.
    induction l.
    constructor.
    constructor.
    {
      rewrite <- in_iff.
      inversion H.
      auto.
    }
    apply IHl.
    inversion H.
    auto.
  }
  intros.
  induction l.
    constructor.
  constructor.
  {
    rewrite in_iff.
    apply NoDup_cons_iff; auto.
  }
  apply IHl.
  inversion H.
  auto.
Qed.
    



Delimit Scope Numeric_scope with Num.
Local Open Scope Num.
Section mdp_numeric. 
  Context {Nt:Type} `{Numerics.Numeric Nt}.
  Record mdp : Type := mdp_mk {
    state : eqType;
    action :  eqType;
    trans : action -> state -> state -> Nt;
    reward : state -> Nt;
    
  }.



  Record mdp_props : Type := mdp_prop_mk {
    p : mdp;
    states : Enumerable (state p);
    actions : Enumerable (action p);
    states_ok : @Enum_ok _ states;
    actions_ok : @Enum_ok _ actions;
    trans_sum1: forall (s : (state p)) (a : (action p)), 
        big_sum states (fun s' => (trans p) a s s') = Numerics.mult_id;
    trans_pos: forall (s1 s2 : (state p)) (a : (action p)),
        0 <= (trans p) a s1 s2 ;
    states_nonempty : (0 <> length states)%nat;
    actions_nonempty : (0 <> length actions)%nat;
  }.
  End mdp_numeric.


  Section mdp.
    Context {Nt:Type} `{Numerics.Numeric Nt}.
    Variable p_props : mdp_props.

    Lemma one_minus_discount_gt_0: forall (discount : Nt) {H : 0 <= discount /\ discount < 1}, 0 < 1 + - discount. 
    Proof.
      intros.
      destruct H0.
      rewrite <- Numerics.plus_neg_r with discount.
      apply Numerics.plus_lt_compat_r; auto.
    Qed.


    Variable discount : Nt.
    Hypothesis discount_ok: 0 <= discount /\ discount < 1.

    Notation action_t := (action (p p_props)).
    Notation state_t := (state (p p_props)).
    Notation p_reward := (reward (p p_props)).
    Notation trans_f := (trans (p p_props)).

    Definition value_func := state_t -> Nt.
    (**Definition value_funcR := state_t -> R.**)
    Definition policy := state_t -> action_t.

    Definition state_list := @enumerable_fun (state_t) (states p_props).
    Definition state_length := length state_list.


      

    Lemma states_In: forall (s : state_t), In s (states p_props).
    Proof.
      intros.
      destruct (states_ok p_props).
      apply enum_total.
    Qed.

    Lemma actions_In: forall (a : action_t), In a (actions p_props).
    Proof.
      intros.
      destruct (actions_ok p_props).
      apply enum_total.
    Qed.

    Definition value_func0  := (fun (x : state_t) => 0).

    Definition discounted_reward (v : value_func) (s : (state_t)) (a : (action_t)) : Nt :=
      (p_reward) s + discount * big_sum (states p_props) (fun  s' =>  (trans_f a s s') * (v s'))%Num.


  Definition value_iteration_step (v : value_func) : value_func := 
    (fun (s : state_t) => 
      mapmax_ne (fun a => discounted_reward v s a) (actions_nonempty p_props)
  ).

    
  Fixpoint value_iteration_rec (v : value_func) (n : nat):=
  match n with
  | O => v
  | S n' => value_iteration_step (value_iteration_rec v  n')
  end.


  Definition value_iteration  (n : nat) :=
    value_iteration_rec (value_func0) n.

  

  Fixpoint evaluate_policy_state (pol : policy) (s : state_t) (i : nat): Nt :=
  match i with 
  | O => p_reward s
  | S i' => p_reward s +
          discount * (big_sum (states p_props)  (fun s' =>  ((trans_f) (pol s) s s') * (evaluate_policy_state pol s' i')))
  end.

  Definition evaluate_policy_step (pol : policy) (v : value_func) : value_func :=
  (fun s => p_reward s + discount * (big_sum (states p_props)) (fun s' => trans_f (pol s) s s' * v s')).

  Definition value_diff  (v1 v2 : value_func) : value_func :=
  (fun s => v1 s + - v2 s).

  Definition value_dist (v1 v2 : value_func) : Nt :=
  mapmax_ne  (fun s => Numerics.abs ((value_diff v1 v2) s) ) (states_nonempty p_props) .


  Fixpoint evaluate_policy_sum (pol : policy) (i : nat): Nt :=
  big_sum (states p_props) (fun s => evaluate_policy_state pol s i).

  Lemma exists_action:  exists a : action_t, In a (actions p_props).
  Proof.
    intros.
    destruct p_props.
    simpl in *.
    destruct actions0.
    { unfold not in actions_nonempty0. exfalso. auto. }
    exists s.
    apply in_eq.
  Qed.
  

  
  Definition head_action : (action_t).
    destruct p_props.
    destruct actions0.
    { simpl in *. exfalso. auto. }
    exact s.
  Defined.

  Definition value_func_policy (v: value_func) : policy :=
  (fun s => argmax_ne
        (fun a=> big_sum (states p_props) (fun s'=> trans_f a s s' * v s' ))
       (actions_nonempty p_props)).
  
  
  

  Definition policy_leq_n  (pol1 pol2 : policy) (n : nat) : Prop :=
  forall (s : state_t), evaluate_policy_state pol1 s n <= evaluate_policy_state pol2 s n.

  Definition policy_leq  (pol1 pol2 : policy) : Prop :=
  forall (s : state_t), exists (n0 : nat), forall (m : nat), (n0 <= m)%nat -> policy_leq_n pol1 pol2 m.



  


  Lemma head_action_correct: Some head_action = hd_error (actions p_props).
  Proof.
    unfold head_action.
    destruct p_props.
    simpl in *.
    destruct actions0; auto.
    exfalso.
    apply actions_nonempty0.
    auto.
  Qed.


  Lemma value_iteration_rec_reverse: forall (v : value_func) (n : nat), value_iteration_rec (value_iteration_step v) n = value_iteration_step (value_iteration_rec v n).
  Proof.
    intros.
    generalize v.
    induction n; intros; simpl; auto; rewrite IHn; auto. 
  Qed.


  Theorem evaluate_policy_contraction: forall (pol : policy) (v1 v2 : value_func),
    value_dist (evaluate_policy_step pol v1) (evaluate_policy_step pol v2) <= discount * value_dist v1 v2.
  Proof.
    intros.
    unfold value_dist.
    unfold evaluate_policy_step.
    unfold value_diff.
    destruct discount_ok.
    apply mapmax_ne_le_const.
    intros.
    rewrite plus_neg_distr.
    rewrite -> plus_comm with (p_reward n) _.
    rewrite plus_assoc.
    rewrite <- plus_assoc with _ (p_reward n) _.
    rewrite plus_neg_r.
    rewrite plus_id_r.
    rewrite neg_mult_distr_r.
    rewrite <- mult_plus_distr_l.
    rewrite abs_mult_pos_l; auto.
    apply mult_le_compat_l; auto.
    rewrite <- big_sum_nmul.
    rewrite <- big_sum_plus.
    rewrite -> big_sum_ext with _ _ state_t (states p_props) (states p_props) _(fun c => trans_f (pol n) n  c * (v1 c + - v2 c)); auto.
    2: {
      unfold eqfun.
      intros.
      rewrite neg_mult_distr_r.
      rewrite mult_plus_distr_l. auto.
    }
    apply le_trans with (big_sum (states p_props) (fun c => abs (trans_f (pol n) n c * (v1 c + - v2 c)))).
      apply big_sum_le_abs.
    rewrite -> big_sum_ext with _ _ state_t (states p_props) (states p_props) _ (fun c => trans_f (pol n) n c * abs (v1 c + - v2 c)); auto.
    2:{ unfold eqfun. intros. apply abs_mult_pos_l. apply (trans_pos _).  }
    apply le_trans with (big_sum (states p_props) (trans_f (pol n) n) * mapmax_ne (fun c => abs ( v1 c + - v2 c)) (states_nonempty p_props)).
      apply big_sum_func_leq_max_l. intros. apply (trans_pos _).
    rewrite (trans_sum1 _).
    rewrite mult_id_l.
    apply le_refl.
  Qed.

  Theorem value_iteration_contraction:  forall  (v1 v2 : value_func),
  value_dist (value_iteration_step v1) (value_iteration_step v2) 
      <= (discount) * (value_dist v1 v2).
  Proof.
    intros.
    unfold value_dist.
    unfold value_iteration_step.
    unfold value_diff.
    unfold discounted_reward.
    destruct discount_ok.
    assert (
      mapmax_ne (l:=states p_props)
      (fun s : state_t =>
       Numerics.abs
         (mapmax_ne (l:=actions p_props)
            (fun a : action_t =>
             p_reward s + discount * big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v1 s'))
            (actions_nonempty p_props) +
          -
          mapmax_ne (l:=actions p_props)
            (fun a : action_t =>
             p_reward s + discount * big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v2 s'))
            (actions_nonempty p_props))) (states_nonempty p_props) =
      mapmax_ne (l:=states p_props)
      (fun s : state_t =>
       discount * Numerics.abs
         (mapmax_ne (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v1 s'))
            (actions_nonempty p_props) +
          -
          mapmax_ne (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v2 s'))
            (actions_nonempty p_props))) (states_nonempty p_props)
      ).
      {        
        apply mapmax_ne_ext.
        intros.
        repeat rewrite <- mapmax_ne_plus_const_l.
        rewrite Numerics.plus_neg_distr.
        rewrite -> Numerics.plus_comm with (- p_reward x) _.
        repeat rewrite <- Numerics.plus_assoc.
        rewrite -> Numerics.plus_comm with (p_reward x) _.
        repeat rewrite <- Numerics.plus_assoc.
        rewrite Numerics.plus_neg_l.
        rewrite Numerics.plus_id_r.
        repeat rewrite <- mapmax_ne_mult_pos_l; auto.
        rewrite Numerics.neg_mult_distr_r.
        rewrite <- Numerics.mult_plus_distr_l.
        rewrite Numerics.abs_mult_pos_l; auto.
      }
      rewrite H2.
      rewrite <- mapmax_ne_mult_pos_l; auto.
      apply Numerics.mult_le_compat_l; auto.
      apply mapmax_ne_le_ext'.
      intros.
      remember (fun a : action_t => big_sum (states p_props) (fun s' : state_t => trans_f a t s' * v1 s')) as f1.
      remember (fun a : action_t => big_sum (states p_props) (fun s' : state_t => trans_f a t s' * v2 s')) as f2.
      apply Numerics.le_trans with (mapmax_ne (fun a => Numerics.abs (f1 a + - f2 a)) (actions_nonempty p_props)).
        apply mapmax_ne_abs_dist_le.
      rewrite Heqf1.
      rewrite Heqf2.
      assert ( 
        mapmax_ne (l:=actions p_props) (fun a : action_t => Numerics.abs (f1 a + - f2 a)) (actions_nonempty p_props) =
        mapmax_ne (l:=actions p_props)
            (fun a : action_t =>
             Numerics.abs
               (big_sum (states p_props) (fun s' : state_t => trans_f a t s' * (v1 s' + - v2 s')))) (actions_nonempty p_props)     
      ).
      {
        apply mapmax_ne_ext.
        intros.
        rewrite Heqf1.
        rewrite Heqf2.
        rewrite <- big_sum_nmul.
        assert (big_sum (states p_props) (fun c : state_t => - (trans_f x t c * v2 c)) =
                big_sum (states p_props) (fun c : state_t => trans_f x t c * - v2 c)
        ).
        { apply big_sum_ext; auto. unfold eqfun. intros. rewrite Numerics.neg_mult_distr_r. auto. }
        rewrite H4.
        rewrite <- big_sum_plus.
        assert (big_sum (states p_props) (fun c : state_t => trans_f x t c * v1 c + trans_f x t c * - v2 c) 
                = big_sum (states p_props) (fun s' : state_t => trans_f x t s' * (v1 s' + - v2 s'))).
        { apply big_sum_ext; auto. unfold eqfun. intros. rewrite Numerics.mult_plus_distr_l. auto. }
        rewrite H5.
        auto.
      }
      rewrite Heqf1 in H4.
      rewrite Heqf2 in H4.
      rewrite H4.
      apply Numerics.le_trans with (
        mapmax_ne (l:=actions p_props)
          (fun a : action_t => (big_sum (states p_props) (fun s' : state_t => trans_f a t s' * Numerics.abs  (v1 s' + - v2 s'))))
          (actions_nonempty p_props) 
      ).
      {
        apply mapmax_ne_le_ext.
        intros.
        apply Numerics.le_trans with ((big_sum (states p_props) (fun s' : state_t => Numerics.abs (trans_f t0 t s' * (v1 s' + - v2 s'))))).
          apply big_sum_le_abs.
        apply big_sum_le; auto.
        intros.
        unfold Numerics.le.
        right.
        apply Numerics.abs_mult_pos_l.
        apply (trans_pos p_props).
      }
      apply Numerics.le_trans with (
        mapmax_ne (l:=actions p_props)
          (fun a : action_t =>  mapmax_ne (fun s' => Numerics.abs (v1 s' + - v2 s')) (states_nonempty p_props))
          (actions_nonempty p_props)
      ).
      {
        apply mapmax_ne_le_ext.
        intro a.
        intros.
        rewrite <- Numerics.mult_id_l.
        rewrite <- (trans_sum1 p_props) with t a.
        apply big_sum_func_leq_max_l.
        intros.
        apply (trans_pos p_props).
      }
      rewrite mapmax_ne_const.
      apply Numerics.le_refl.
    Qed.

  Lemma discount_ge0: 0 <= discount.
  Proof. intuition. Qed.

  Lemma discount_lt1: discount < 1.
  Proof. intuition. Qed.

 Lemma value_iteration_step_ext: forall (v1 v2 : value_func),
    (forall s : state_t, v1 s = v2 s) -> (forall s : state_t, (value_iteration_step v1) s = (value_iteration_step v2) s).
  Proof.
    intros.
    unfold value_iteration_step.
    apply mapmax_ne_ext.
    intros.
    unfold discounted_reward.
    apply plus_simpl_l.
    apply mult_simpl_l.
    apply big_sum_ext; auto.
    unfold eqfun. intros.
    rewrite H0.
    auto.
  Qed.

  Lemma evaluate_policy_step_ext: forall (pol : policy) (v1 v2 : value_func) ,
    (forall s : state_t, v1 s = v2 s) -> (forall s : state_t, (evaluate_policy_step pol v1) s = (evaluate_policy_step pol v2) s).
  Proof.
    intros.
    unfold evaluate_policy_step.
    rewrite -> big_sum_ext with _ _ _ _ (states p_props) _ (fun s' => trans_f (pol s) s s' * v2 s'); auto.
    unfold eqfun.
    intros.
    rewrite H0.
    auto.
  Qed.
    

  Definition value_iteration_banach : banach.contraction_func :=
    banach.contraction_mk 
      Nt _
      state_t
      (states p_props)
      (states_ok p_props)
      discount
      (states_nonempty p_props)
      value_iteration_step
      discount_ge0
      discount_lt1
      value_iteration_step_ext
      value_iteration_contraction
    .


  Definition evaluate_policy_banach (pol : policy) : banach.contraction_func :=
    banach.contraction_mk 
      Nt _
      state_t
      (states p_props)
      (states_ok p_props)
      discount
      (states_nonempty p_props)
      (evaluate_policy_step pol)
      discount_ge0
      discount_lt1
      (evaluate_policy_step_ext pol)
      (evaluate_policy_contraction pol)
    .

  Definition evaluate_policy_rec (pol : policy) := banach.rec_f (evaluate_policy_banach pol).

  Lemma evaluate_policy_rec_state_same: forall (pol : policy) (n : nat) (s : state_t),
      evaluate_policy_state pol s n = (evaluate_policy_rec pol (fun s' => p_reward s') n) s.
  Proof.
    intros.
    generalize s.
    induction n; auto.
    intros.
    unfold evaluate_policy_rec in *.
    simpl in *.
    unfold evaluate_policy_step.
    rewrite -> big_sum_ext with _ _ _ _ (states p_props) _ 
      (fun s' => trans_f (pol s0) s0 s' * banach.rec_f (evaluate_policy_banach pol) [eta p_reward] n s'); auto.
    unfold eqfun.
    intros.
    rewrite IHn.
    auto.
  Qed.


  Lemma value_dist_banach_dist: forall (v1 v2 : value_func), value_dist v1 v2 = banach.max_dist _ (states_nonempty p_props) v1 v2.
  Proof. auto. Qed.

  Lemma value_iteration_rec_banach_rec: forall (v : state_t -> Nt) (n : nat), 
      value_iteration_rec v n = banach.rec_f value_iteration_banach v n.
  Proof. auto. Qed.

  Lemma value_dist_same_0: forall (v1 v2 : value_func), (forall s : state_t, v1 s = v2 s) -> value_dist v1 v2 = 0.
  Proof. apply (banach.eq_dist_0 value_iteration_banach). Qed.

  Lemma value_dist_triangle: forall (v1 v2 v3: value_func), value_dist v1 v3 <= 
        value_dist v1 v2 + value_dist v2 v3.
  Proof. intros. apply (banach.dist_triangle (value_iteration_banach)). Qed.

  Lemma value_dist_ge0: forall (v1 v2 : value_func), 0 <= value_dist v1 v2.
  Proof.
    intros.
    unfold value_dist.
    rewrite <- mapmax_ne_const with _ _ _ _ 0 (states_nonempty p_props).
    apply mapmax_ne_le_ext.
    intros.
    apply Numerics.abs_ge_0.
  Qed.


  Lemma value_dist_comm: forall (v1 v2 : value_func), value_dist v1 v2 = value_dist v2 v1.
  Proof. 
    intros.
    unfold value_dist.
    apply mapmax_ne_ext.
    intros.
    unfold value_diff.
    rewrite <- abs_neg.
    rewrite plus_neg_distr. rewrite double_neg. rewrite plus_comm. auto.
  Qed. 

    Lemma value_iteration_converge_aux: forall (v1 v2 : value_func) (n : nat), 
      value_dist (value_iteration_rec v1 n) (value_iteration_rec v2 n) <= (Numerics.pow_nat discount n) * (value_dist v1 v2).
    Proof. intros. apply (banach.rec_dist value_iteration_banach). Qed.


    Lemma value_dist_rec_ub: forall (v : value_func) (n : nat),
      (1 + - discount) * value_dist (value_iteration_rec v n) v <= (1 + - pow_nat discount n) * value_dist v (value_iteration_step v).
    Proof. intros. apply (banach.dist_step_rec_n_ub value_iteration_banach). Qed.  

  Lemma value_iteration_rec_plus: forall (v : value_func) (n m: nat), value_iteration_rec v (n + m) = value_iteration_rec (value_iteration_rec v n) m.
  Proof.
    intros.
    induction m.
    { rewrite addn0. auto. }
    rewrite addnS.
    simpl.
    rewrite IHm.
    auto.
  Qed.

  Lemma value_dist_0_same: forall (v1 v2 : value_func), value_dist v1 v2 = 0 -> forall s, v1 s = v2 s.
  Proof. apply (banach.dist_0_eq value_iteration_banach). Qed.

  Lemma discount0_no_change: forall (v1 v2 : value_func) (n m : nat) (s : state_t), 
      discount = 0 -> (value_iteration_rec v1 (S n)) s = (value_iteration_rec v2 (S m)) s.
  Proof. intros. apply value_dist_0_same. apply (banach.q0_rec0 value_iteration_banach). auto. Qed.

  
  Lemma value_iteration_converge_aux': forall (v : value_func) (n m : nat),
    (1 + - discount) * value_dist (value_iteration_rec v n) (value_iteration_rec v (n+m)%nat) <=
    value_dist v (value_iteration_step v) *  Numerics.pow_nat discount n. 
  Proof. apply (banach.rec_f_nm_ub value_iteration_banach). Qed. 

 Lemma value_dist_ub: forall (s : state_t) (v1 v2 : value_func), Numerics.abs ((v1 s) + - (v2 s)) <= value_dist v1 v2.
  Proof. 
    intros.
    unfold value_dist.
    unfold value_diff.
    remember (fun s' => Numerics.abs (v1 s' + - v2 s')) as f.
    assert (Numerics.abs (v1 s + - v2 s) = f s).
      rewrite Heqf. auto.
    rewrite H0.
    apply mapmax_ne_correct.
    apply states_In.
  Qed.


  Lemma value_func_eval_ub: forall (s : state_t)(p : policy) (n : nat),
    evaluate_policy_state p s n <=  (value_iteration_rec p_reward n) s.
  Proof.
    intros.
    generalize p0 s.
    induction n; intros.
      simpl. apply le_refl.
    simpl.
    destruct discount_ok.
    unfold value_iteration_step.
    unfold discounted_reward.
    rewrite <- mapmax_ne_plus_const_l.
    apply plus_le_compat_l.
    rewrite <- mapmax_ne_mult_pos_l; auto.
    apply mult_le_compat_l; auto.
    remember ((fun n0 : action_t =>
       big_sum (states p_props) (fun s' : state_t => trans_f n0 s0 s' * value_iteration_rec p_reward n s')))
      as f.
    apply le_trans with (f (p1 s0)).
    2: { apply mapmax_ne_correct. apply actions_In. }
    rewrite Heqf.
    apply big_sum_le.
    intros.
    apply mult_le_compat_l.
      apply (trans_pos p_props).
    apply IHn.
  Qed.

 


  Fixpoint policy_value_iteration (n : nat) (s : state_t) :=
  match n with
  | O=> argmax_ne (l:=actions p_props) (fun f => 0) (actions_nonempty p_props)
  | S n' => argmax_ne (fun a=> big_sum 
      (states p_props) (fun s' => trans_f a s s' * evaluate_policy_state (policy_value_iteration n') s' n'))
      (actions_nonempty p_props)
  end.

 End mdp.

  Section mdp_to_R.
    Context {Nt:Type} `{Numerics.Numeric Nt}.

    Definition mdp_to_R (p : @mdp Nt) : @mdp R :=
     mdp_mk (state p) (action p) (fun a s s' => to_R ((trans p) a s s')) (fun s => to_R ((reward p) s)).


    Program Definition mdp_prop_to_R (m : @mdp_props Nt H) : @mdp_props R _ :=
      mdp_prop_mk (mdp_to_R (p m)) (states m) (actions m) (states_ok m) (actions_ok m) _ _ (states_nonempty m) (actions_nonempty m).
    Next Obligation.
      rewrite to_R_big_sum.
      rewrite (trans_sum1 m).
      apply to_R_mult_id.
    Qed.
    Next Obligation.
      rewrite <- to_R_plus_id.
      rewrite <- to_R_le.
      apply (trans_pos m).
    Qed.



    Variable p_props : mdp_props.
    Variable discount : Nt.
    Hypothesis discount_ok: 0 <= discount /\ discount < 1.

    Notation action_t := (action (p p_props)).
    Notation state_t := (state (p p_props)).
    Notation p_reward := (reward (p p_props)).
    Notation trans_f := (trans (p p_props)).



  Lemma to_R_value_iteration_step: forall (v : value_func p_props) (s : state_t), 
      to_R ((value_iteration_step _ discount v) s)  = (value_iteration_step (mdp_prop_to_R p_props) (to_R discount) (fun s' : state_t => to_R (v s'))) s.
  Proof.
    intros.
    destruct discount_ok.
    unfold value_iteration_step.
    rewrite to_R_mapmax_ne.
    apply mapmax_ne_ext.
    intros.
    unfold discounted_reward.
    simpl.
    rewrite -> big_sum_ext with R _ state_t (states p_props) (states p_props) _  (fun s' : state_t => to_R ((trans_f x s s') * (v s'))); auto.
    2: { unfold eqfun. intros. apply to_R_mult. }
    rewrite to_R_big_sum.
    rewrite to_R_mult.
    rewrite to_R_plus.
    auto.
  Qed.
      

  Lemma to_R_value_iteration_rec: forall (v : value_func p_props) (s : state_t) (n : nat), 
      to_R ((value_iteration_rec _ discount v n) s)  = (value_iteration_rec (mdp_prop_to_R p_props) (to_R discount) (fun s' : state_t => to_R (v s')) n) s.
  Proof.
    intros.
    generalize s.
    induction n; intros; simpl; auto.
    repeat rewrite value_iteration_rec_reverse.
    rewrite to_R_value_iteration_step.
    apply value_iteration_step_ext.
    apply IHn.
  Qed.




  End mdp_to_R.
  Section mdp_R. 
    Variable p_props : @mdp_props R _.
    Variable discount : R.
    Hypothesis discount_ok: 0 <= discount /\ discount < 1.

    Lemma R_discount_ge0: 0 <= discount.
    Proof. destruct discount_ok. auto. Qed.

    Lemma R_discount_lt1: discount < 1.
    Proof. destruct discount_ok. auto. Qed.


    Definition value_iteration_R_banach : @banach.contraction_func R _:=
      banach.contraction_mk 
        R _
        (state (p p_props))
        (states p_props)
        (states_ok p_props)
        discount
        (states_nonempty p_props)
        (value_iteration_step p_props discount)
        R_discount_ge0
        R_discount_lt1
        (value_iteration_step_ext p_props discount)
        (value_iteration_contraction p_props discount discount_ok).
      

    Definition evaluate_policy_R_banach (pol : policy p_props) : @banach.contraction_func R _:=
      banach.contraction_mk 
        R _
        (state (p p_props))
        (states p_props)
        (states_ok p_props)
        discount
        (states_nonempty p_props)
        (evaluate_policy_step p_props discount pol)
        R_discount_ge0
        R_discount_lt1
        (evaluate_policy_step_ext p_props discount pol)
        (evaluate_policy_contraction p_props discount discount_ok pol).
      

    


    Lemma value_iteration_R_cauchy_crit_aux: forall (v : value_func p_props) (n m : nat) (e: R), 
      0 < e -> 
      0 < value_dist p_props v (value_iteration_step p_props discount v) ->
      pow_nat discount n < e * (1 + - discount) * Rinv  (value_dist p_props v (value_iteration_step p_props discount v)) ->
      value_dist p_props (value_iteration_rec p_props discount v n) (value_iteration_rec p_props discount v (n + m)) < e.
    Proof. apply (banach.contraction_cauchy_crit_aux value_iteration_R_banach). Qed.

    Lemma value_iteration_R_cauchy_crit: forall (v : value_func p_props) (s : (state (p p_props))), Cauchy_crit (fun n => (value_iteration_rec _ discount v n s)).
    Proof. intros. apply (banach.contraction_cauchy_crit value_iteration_R_banach). Qed.

    
    Lemma value_iteration_R_limit_same: forall (v1 v2 : value_func p_props) (s : (state (p p_props))) (x : R), 
      Un_cv (fun n => (value_iteration_rec _ discount v1 n) s) x -> Un_cv (fun n => (value_iteration_rec _ discount v2 n) s) x.
    Proof. apply (banach.limit_unique value_iteration_R_banach). Qed.

     
    Definition converge_value_func := banach.converge_func value_iteration_R_banach.
    Definition converge_eval_func (p : policy p_props) := banach.converge_func (evaluate_policy_R_banach p).

   
    Lemma converge_value_func_correct: forall (v : value_func p_props) (s : state (p p_props)),
      Un_cv (fun n => (value_iteration_rec _ discount v n) s) (converge_value_func s).
    Proof. apply (banach.converge_func_correct value_iteration_R_banach). Qed.

    
    Lemma value_iteration_step_converge_0: forall (v : value_func p_props), Un_cv (fun n => value_dist p_props (value_iteration_rec _ discount v n)
         (value_iteration_step _ discount (value_iteration_rec _ discount v n))) 0.
    Proof.  apply (banach.step_converge0 value_iteration_R_banach). Qed. 



    Lemma value_func_converge_strong: forall (v : value_func p_props) (eps : R),
            0 < eps -> exists N : nat, forall (s : state (p p_props)), forall n : nat, (n >= N)%coq_nat ->
              R_dist (value_iteration_rec p_props discount v n s)
                 (converge_value_func s) < eps.
    Proof. apply (banach.func_converge_strong value_iteration_R_banach). Qed.

    Lemma value_iteration_fixpoint: forall (s : (state (p p_props))),
      (value_iteration_step p_props discount converge_value_func) s = converge_value_func s.
    Proof. apply (banach.rec_fixpoint value_iteration_R_banach). Qed.

    Lemma value_iteration_R_converge: forall (v : value_func p_props) (s : (state (p p_props))), exists r : R, Un_cv (fun n => (value_iteration_rec _ discount v n) s) r.
    Proof.
     intros.
      destruct R_complete with ((value_iteration_rec p_props discount v)^~ s); eauto.
      apply value_iteration_R_cauchy_crit.
    Qed.

    Lemma value_iteration_eval_step_fixpoint: forall s : state (p p_props),
      evaluate_policy_step _ discount (value_func_policy _ converge_value_func) converge_value_func s =
      converge_value_func s.
    Proof.
      intros.
      unfold evaluate_policy_step.
      destruct discount_ok.
      rewrite <- value_iteration_fixpoint.
      unfold value_iteration_step.
      unfold discounted_reward.
      rewrite <- mapmax_ne_plus_const_l.
      apply plus_simpl_l.
      rewrite <- mapmax_ne_mult_pos_l; auto.
      apply mult_simpl_l.
      unfold value_func_policy.
      rewrite argmax_ne_mapmax_ne.
      apply big_sum_ext; auto.
    Qed.

    Lemma value_iteration_eval_limit_same: forall s, converge_value_func s = converge_eval_func (value_func_policy _ converge_value_func)  s.
    Proof.
      intros.
      apply (banach.fixpoint_unique (evaluate_policy_R_banach  (value_func_policy p_props converge_value_func))).
      intros.
      simpl.
      rewrite <- value_iteration_eval_step_fixpoint. auto.
    Qed.

    Lemma value_iteration_limit_opt: forall (s : state (p p_props)) pol,
      converge_eval_func pol s <= converge_eval_func (value_func_policy _ converge_value_func) s.
    Proof.
      intros.
      rewrite <- value_iteration_eval_limit_same.
      apply RiemannInt.Rle_cv_lim with 
        (fun n => (evaluate_policy_rec _ discount discount_ok pol (reward (p p_props)) n) s)
        (fun n => (value_iteration_rec _ discount (reward (p p_props)) n) s).
      2: { apply (banach.converge_func_correct (evaluate_policy_R_banach pol)). }
      2: { apply converge_value_func_correct. }
      intros.
      rewrite <- evaluate_policy_rec_state_same.
      rewrite <- R_le_same.
      apply value_func_eval_ub. auto.
    Qed.

End mdp_R.

(**
  
Definition states : list nat := ([O; S O; S (S O); 3; 4 ; 5])%nat.
Definition actions := [O; S O; S (S O)].

Definition reward (s : nat) : DRed.t :=
match s with
| 0%nat => DRed.opp 1
| 1%nat => 1
| 2%nat => 1
| 3%nat => DRed.opp 1
| 4%nat => DRed.opp 1
| 5%nat => 1 + 1
| _ => 0
end.


Program Definition DRedHalf := DRed.mk (Dmake 1 1) _.

Definition trans (a s1 s2 : nat) : DRed.t :=
match (s1, a, s2) with
| (0, 0, 0)%nat => 1
| (0, 1, 3)%nat => 1
| (0, 2, 1)%nat => 1
| (1, 0, 1)%nat => DRedHalf
| (1, 0, 0)%nat => DRedHalf
| (1, 1, 0)%nat => DRedHalf
| (1, 1, 4)%nat => DRedHalf
| (1, 2, 3)%nat => 1
| (2, 0, 1)%nat => DRedHalf
| (2, 0, 2)%nat => DRedHalf
| (2, 1, 5)%nat => DRedHalf
| (2, 1, 1)%nat => DRedHalf
| (2, 2, 2)%nat => 1
| (3, 0, 0)%nat => 1
| (3, 1, 3)%nat => 1
| (3, 2, 4)%nat => 1
| (4, 0, 3)%nat => DRedHalf
| (4, 0, 1)%nat => DRedHalf
| (4, 1, 3)%nat => DRedHalf
| (4, 1, 4)%nat => DRedHalf
| (4, 2, 5)%nat => 1
| (5, 0, 2)%nat => DRedHalf
| (5, 0, 4)%nat => DRedHalf
| (5, 1, 4)%nat => DRedHalf
| (5, 1, 5)%nat => DRedHalf
| (5, 2, 5)%nat => 1
| (_, _, _) => 0
end.
 
Definition Vi := [0; 0; 0; 0; 0; 0].

Lemma transFuncSum1:  forall (s : nat) (a : nat), 
        List.In s states -> big_sum states (fun s' => trans a s s') = DRed.t1.
Proof.
  Admitted.

Lemma states_nonempty: (0 < length states)%nat.
Proof. simpl. unfold Peano.lt. repeat constructor. Qed.

Lemma actions_nonempty: (0 < length actions)%nat.
Proof. simpl. unfold Peano.lt. repeat constructor. Qed.

Definition discount := DRedHalf.

Lemma discount_ok: (lt plus_id discount /\ lt discount mult_id)%Num.
Proof. Admitted.

Definition p := mdp_mk
    DRed.t nat nat states actions trans reward discount transFuncSum1 discount_ok states_nonempty actions_nonempty.


Definition Test := (ValueIteration DRed.t p).



Extraction Language Ocaml.
Extraction "value_iteration.ml" Test.
Extraction "value_iteration.ml" Test.




Fixpoint EvaluatePolicy (mvp : MVP) (discount : float32) (policy : State->Action) (s : State) (steps : nat) : float32 :=
match steps with
| O => 0
| S n' => (R mvp) s + 
        discount * Sum (fun s' =>  ((P mvp) (policy s) s s') * (EvaluatePolicy mvp discount policy s' n')) (St mvp)
end.




Definition DiscountedReward (mvp : MVP) (v : ValueFunc) (discount : float32) (s : State) (a : Action) : float32:=
SumStates (St mvp) (fun s' =>  (R mvp) s + ((P mvp) a s s') *  discount * ((v s'))).


Definition value_diff (V1 V2: ValueFunc) : ValueFunc :=
(fun s => ((V1 s) + (f32_opp (V2 s))) ).

Definition value_dist (V1 : ValueFunc) (V2 : ValueFunc) (s : States): float32 :=
(value_max (value_diff V1 V2) s).



**)
