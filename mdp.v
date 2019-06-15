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

Require Import FunctionalExtensionality.

(**Open Scope f32_scope.**)


Require Import OUVerT.numerics.
Require Import OUVerT.generalized_bigops.
Require Import OUVerT.dyadic.
Require Import ProofIrrelevance.

Require Import OUVerT.compile.

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
    
(***

Definition cons_all {T : Type} (x : T) (l : list (list T)) : list (list T) :=
map (fun l' => x :: l') l.

Definition cons_all_from {T : Type} (l1 : list T) (l2 : list (list T)) : list (list T) :=
seq.flatten (map (fun x => cons_all x l2) l1).



(** |l1| ^ n **)
Fixpoint all_perm_rep {T : Type} (l : list T) (n : nat) : list (list T) := 
match n with
| O => []
| S O => map (fun x => [x]) l
| S n' => cons_all_from l (all_perm_rep l n')
end.


Fixpoint  all_perm_rep_funcs {T1 T2 : Type} (l1 : list T1) (l2 : list T2) : list (T1 -> T2) :=
match l1 with
| [] => []
| [x] => (map (fun y=>[(x,y)]) l2)
| x :: l1' => cons_all_from (map (fun y => (x , y) ) l2) (all_perm_rep_l2 l1' l2)
end.

**)



Delimit Scope Numeric_scope with Num.
Local Open Scope Num.
Section mdp_numeric. 
  Context (Nt:Type) `{Numerics.Numeric Nt}.
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

  Section mdp.
    Variable p_props : mdp_props.
    Variable discount : Nt.
    Hypothesis discount_ok: Numerics.plus_id <= discount /\ discount < Numerics.mult_id.

    Notation action_t := (action (p p_props)).
    Notation state_t := (state (p p_props)).
    Notation p_reward := (reward (p p_props)).
    Notation trans_f := (trans (p p_props)).

    
    Definition value_func := state_t -> Nt.
    Definition policy := state_t -> action_t.

    (**

    Definition mk_policy_list_aux (s : state_t) (a_list : list action_t) : 
            list (state_t -> action_t) :=
    map (fun a => (fun s=>a)) a_list.

    



    Definition mk_policy_list (s_list : list state_t) (a_list : list action_t) : 
              list (state_t -> action_t) :=
    fold_left  (fun x y => app x y) (map (fun s => mk_policy_list_aux s a_list) s_list) [].


    Definition all_policies := mk_policy_list (states p_props) (actions p_props).

    Lemma policy_aux_nodup: forall s : state_t, SetoidList.NoDupA (fun x y: policy => x = y) 
          (mk_policy_list_aux s (actions p_props)).
    Proof.
      intros.
      rewrite no_dup_iff.
      unfold mk_policy_list_aux.
      apply FinFun.Injective_map_NoDup.
      {
        unfold FinFun.Injective.
        intros.
        
        destruct x.
        inversion H0.
        destruct H0.
        Print functional_extensionality.
        rewrite <- functional_extensionality in H0.
        apply functional_extensionalily
        

 Print FinFun.Injective.
      SearchAbout NoDup.
      
      
      induction (actions p_props); simpl; auto.
      constructor.
      {
        

    Lemma policy_nodup: SetoidList.NoDupA (fun x y: policy => x = y) all_policies.
    Proof.
      unfold all_policies.
      generalize (actions p_props).
      induction (states p_props); simpl; auto.
      intros.
      apply SetoidList.NoDupA_app; auto.
      {
        apply IHe.
        induction e0; simpl; auto.
        
        Print SetoidList.NoDupA .
        constructor 2.
        { 
        apply IHe.
      apply SetoidList.NoDupA_split.
      SearchAbout SetoidList.NoDupA.
      simpl.
      constructor.
      induction (actions p_props); simpl; auto.
      
      constructor.
      constructor.
      unfold not.
      intros.
      inversion H0.
      inversion H2.
      inversion H2.
      constructor.
      unfold not.
      intros.
      inversion H0.
      constructor.
    Qed.


    Instance policy_enum : Enumerable policy :=
       mk_policy_list (states p_props) (actions p_props).

     Instance  policy_ok : @Enum_ok policy (mk_policy_list (states p_props) (actions p_props)).
      
      constructor.
      {
        induction (enumerate policy); auto.
        inversion IHl.
        { 
          constructor; auto.
          rewrite SetoidList.InA_nil.
          auto.
        }
        inversion H1.
        { 
        constructor.
        { 

        simpl.
          SearchAbout SetoidList.InA.
          constructor.
          simpl.
        
        constructor.
        { 
        apply SetoidList.NoDupA_cons.
        { Print SetoidList.NoDupA. in IHl.
        SearchAbout SetoidList.NoDupA.
        simpl.        
        


  **)

    Definition value_func0  := (fun (x : state_t) => Numerics.plus_id).

    Definition discounted_reward (v : value_func) (s : (state_t)) (a : (action_t)) : Nt :=
      (p_reward) s + discount * big_sum (states p_props) (fun  s' =>  (trans_f a s s') * (v s'))%Num.


  Definition value_iteration_step (v : value_func) : value_func := 
    (fun (s : state_t) => 
      num_nonempty_mapmax (fun a => discounted_reward v s a) (actions_nonempty p_props)
  ).

    
  Fixpoint value_iteration_rec (v : value_func) (n : nat):=
  match n with
  | O => v
  | S n' => value_iteration_rec (value_iteration_step v) n'
  end.

  Definition value_iteration  (n : nat) :=
    value_iteration_rec (value_func0) n.


  Fixpoint evaluate_policy_state (pol : policy) (s : state_t) (i : nat): Nt :=
  match i with 
  | O => p_reward s
  | S i' => p_reward s +
          discount * (big_sum (states p_props)  (fun s' =>  ((trans_f) (pol s) s s') * (evaluate_policy_state pol s' i')))
  end.

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
  
  Definition value_diff  (v1 v2 : value_func) : value_func :=
  (fun s => v1 s + - v2 s).

  Definition value_dist (v1 v2 : value_func) : Nt :=
  num_nonempty_mapmax  (fun s => Numerics.abs ((value_diff v1 v2) s) ) (states_nonempty p_props) .

  
  Definition head_action : (action_t).
    destruct p_props.
    destruct actions0.
    { simpl in *. exfalso. auto. }
    exact s.
  Defined.

  Print head.

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
 
  Definition value_func_policy (v: value_func) : policy :=
  (fun s => num_nonempty_argmax  (fun a => discounted_reward v s a) (actions_nonempty p_props)).
  

  

  Definition policy_leq_n  (pol1 pol2 : policy) (n : nat) : Prop :=
  forall (s : state_t), evaluate_policy_state pol1 s n <= evaluate_policy_state pol2 s n.

  Definition policy_leq  (pol1 pol2 : policy) : Prop :=
  forall (s : state_t), exists (n0 : nat), forall (m : nat), (n0 <= m)%nat -> policy_leq_n pol1 pol2 m.

  (**Fixpoint policy_opt  (n : nat) : policy :=
   match n with
   | O =>
      (fun s => head_action)
   | S n' => fun s => (
      num_nonempty_argmax (fun a => 
          big_sum (states p_props) (fun s' => trans_f a s s' * evaluate_policy_state (policy_opt n') s' n)   
        ) (actions_nonempty p_props)
    )
   end.**)

  Lemma value_iteration_rec_reverse: forall (v : value_func) (n : nat), value_iteration_rec (value_iteration_step v) n = value_iteration_step (value_iteration_rec v n).
  Proof.
    intros.
    generalize v.
    induction n; simpl; auto. 
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
      num_nonempty_mapmax (l:=states p_props)
      (fun s : state_t =>
       Numerics.abs
         (num_nonempty_mapmax (l:=actions p_props)
            (fun a : action_t =>
             p_reward s + discount * big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v1 s'))
            (actions_nonempty p_props) +
          -
          num_nonempty_mapmax (l:=actions p_props)
            (fun a : action_t =>
             p_reward s + discount * big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v2 s'))
            (actions_nonempty p_props))) (states_nonempty p_props) =
      num_nonempty_mapmax (l:=states p_props)
      (fun s : state_t =>
       discount * Numerics.abs
         (num_nonempty_mapmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v1 s'))
            (actions_nonempty p_props) +
          -
          num_nonempty_mapmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props) (fun s' : state_t => trans_f a s s' * v2 s'))
            (actions_nonempty p_props))) (states_nonempty p_props)
      ).
      {        
        apply num_nonempty_mapmax_ext.
        intros.
        repeat rewrite <- num_nonempty_mapmax_plus_const_l.
        rewrite Numerics.plus_neg_distr.
        rewrite -> Numerics.plus_comm with (- p_reward x) _.
        repeat rewrite <- Numerics.plus_assoc.
        rewrite -> Numerics.plus_comm with (p_reward x) _.
        repeat rewrite <- Numerics.plus_assoc.
        rewrite Numerics.plus_neg_l.
        rewrite Numerics.plus_id_r.
        repeat rewrite <- num_nonempty_mapmax_mult_pos_l; auto.
        rewrite Numerics.neg_mult_distr_r.
        rewrite <- Numerics.mult_plus_distr_l.
        rewrite Numerics.abs_mult_pos_l; auto.
      }
      rewrite H2.
      rewrite <- num_nonempty_mapmax_mult_pos_l; auto.
      apply Numerics.mult_le_compat_l; auto.
      apply num_nonempty_mapmax_le_ext'.
      intros.
      remember (fun a : action_t => big_sum (states p_props) (fun s' : state_t => trans_f a t s' * v1 s')) as f1.
      remember (fun a : action_t => big_sum (states p_props) (fun s' : state_t => trans_f a t s' * v2 s')) as f2.
      apply Numerics.le_trans with (num_nonempty_mapmax (fun a => Numerics.abs (f1 a + - f2 a)) (actions_nonempty p_props)).
        apply num_nonempty_mapmax_abs_dist_le.
      rewrite Heqf1.
      rewrite Heqf2.
      assert ( 
        num_nonempty_mapmax (l:=actions p_props) (fun a : action_t => Numerics.abs (f1 a + - f2 a)) (actions_nonempty p_props) =
        num_nonempty_mapmax (l:=actions p_props)
            (fun a : action_t =>
             Numerics.abs
               (big_sum (states p_props) (fun s' : state_t => trans_f a t s' * (v1 s' + - v2 s')))) (actions_nonempty p_props)     
      ).
      {
        apply num_nonempty_mapmax_ext.
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
        num_nonempty_mapmax (l:=actions p_props)
          (fun a : action_t => (big_sum (states p_props) (fun s' : state_t => trans_f a t s' * Numerics.abs  (v1 s' + - v2 s'))))
          (actions_nonempty p_props) 
      ).
      {
        apply num_nonempty_mapmax_le_ext.
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
        num_nonempty_mapmax (l:=actions p_props)
          (fun a : action_t =>  num_nonempty_mapmax (fun s' => Numerics.abs (v1 s' + - v2 s')) (states_nonempty p_props))
          (actions_nonempty p_props)
      ).
      {
        apply num_nonempty_mapmax_le_ext.
        intro a.
        intros.
        rewrite <- Numerics.mult_id_l.
        rewrite <- (trans_sum1 p_props) with t a.
        apply big_sum_func_leq_max_l.
        intros.
        apply (trans_pos p_props).
      }
      rewrite num_nonempty_mapmax_const.
      apply Numerics.le_refl.
    Qed.
    
    

  Theorem value_iteration_monotonic: forall (v : value_func), 
      policy_value_leq (value_func_policy v) (value_func_policy (value_iteration_step v)).
  Admitted.

  Theorem policy_max: forall (p : mdp), exists x : Nt, 
    (forall (pol : policy) (n : nat), evaluate_policy_all pol n <= x).
  Admitted.


  Lemma value_iteration_converge_aux: forall (v : value_func) (n : nat), 
      value_dist (value_iteration_rec v n) (value_iteration_rec v (S n)) <= (Numerics.pow_nat discount n) * (value_dist v (value_iteration_step v ) ).
  Proof.
    intros.
    induction n.
    {
      simpl.
      rewrite Numerics.pow_natO.
      rewrite Numerics.mult_id_l.
      apply Numerics.le_refl.
    }
    simpl in IHn.
    rewrite Numerics.pow_nat_rec.
    simpl.
    repeat rewrite value_iteration_rec_reverse.
    apply Numerics.le_trans with (
      discount *      
      value_dist ((value_iteration_rec v n))
      (value_iteration_step ((value_iteration_rec v n)))
    ).
    { apply value_iteration_contraction. }
    destruct discount_ok.
    apply Numerics.mult_le_compat; auto.
    { unfold value_dist. 

    SearchAbout Numerics.le.
    assert (value_dist (value_iteration_step (value_iteration_rec v n))
      (value_iteration_step (value_iteration_step (value_iteration_rec v n))) <= discount * value_dist ((value_iteration_rec v n))
      (value_iteration_step ( (value_iteration_rec v n)))).
    SearchAbout 
    { apply value_iteration_contraction. }
    


  Theorem value_iteration_converge: forall  (v : value_func) (eps : Nt), exists n0 : nat, 
       forall (n m : nat), Numerics.abs ( value_dist (value_iteration_rec v n) (value_iteration_rec v m)  ) < eps.
  Admitted.

  Fixpoint policy_opt_eval (s : state_t) (n : nat)  : Nt :=
   match n with
   | O => p_reward s
   | S n' => (p_reward s) + discount * num_nonempty_mapmax
       (fun a=> big_sum (states p_props) (fun s' => trans_f a s s' * policy_opt_eval  s' n' ))
       (actions_nonempty p_props)
  end.
 
  Definition policy_opt (n : nat) := value_func_policy (fun s => policy_opt_eval s n).

  Lemma policy_opt_eval_correct: forall (n : nat) (s : state_t), 
      evaluate_policy_state (policy_opt n) s n = policy_opt_eval s n.
  Proof.
    intros.
    generalize dependent s.
    induction n; auto.
    intros.
    simpl in *.
    apply Numerics.plus_simpl_l.
    apply Numerics.mult_simpl_l.
    unfold policy_opt.
    unfold value_func_policy.
    simpl.
    
    
    remember ((num_nonempty_argmax (l:=actions p_props)
        [eta discounted_reward
               (fun s0 : state_t =>
                p_reward s0 +
                discount *
                num_nonempty_mapmax (l:=actions p_props)
                  (fun a0 : action_t =>
                   big_sum (states p_props) (fun s'0 : state_t => trans_f a0 s0 s'0 * policy_opt_eval s'0 n))
                  (actions_nonempty p_props)) s] (actions_nonempty p_props))) as f.
    assert (big_sum (states p_props)
      (fun s' : state_t =>
       trans_f f s s' *
       evaluate_policy_state
         (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            [eta discounted_reward
                   (fun s1 : state_t =>
                    p_reward s1 +
                    discount *
                    num_nonempty_mapmax (l:=actions p_props)
                      (fun a0 : action_t =>
                       big_sum (states p_props) (fun s'0 : state_t => trans_f a0 s1 s'0 * policy_opt_eval s'0 n))
                      (actions_nonempty p_props)) s0] (actions_nonempty p_props)) s' n) =
       big_sum (states p_props)
      (fun s' : state_t =>
       trans_f f s s' *
       evaluate_policy_state
         (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            [eta discounted_reward
                   (fun s1 : state_t =>
                    p_reward s1 +
                    discount *
                    num_nonempty_mapmax (l:=actions p_props)
                      (fun a0 : action_t =>
                       big_sum (states p_props) (fun s'0 : state_t => trans_f a0 s1 s'0 * policy_opt_eval s'0 n))
                      (actions_nonempty p_props)) s0] (actions_nonempty p_props)) s' n)


)
    remember ((fun a : action_t =>
            big_sum (states p_props) (fun s'0 : state_t => trans_f a s0 s'0 * policy_opt_eval s'0 n))) as f.


    remember (fun s => (fun a : action_t =>
         big_sum (states p_props)
           (fun s'0 : state_t =>
            trans_f a s s'0 *
            (p_reward s'0 +
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))) as f.
    assert (
        big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s0 s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s' n)
      =
       big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (f s)
              (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (f s0)
              (actions_nonempty p_props)) s' n)
    ). rewrite Heqf. auto.
    rewrite H0.
    


    remember (fun (s : state_t) (a : action_t) (n' : nat) (f' : state_t -> nat -> Nt) => big_sum (states p_props) (fun s' => trans_f a s s' * discount * f'  s' n' )) as f.
    assert (
      big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s0 s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s' n) = 
        big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s s'0 *
                  (p_reward s'0 +                   
                  (f s'0 (policy_opt n s'0) n (evaluate_policy_state (policy_opt n)))
                  (**big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n) **) )))
              (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s0 s'0 *
                  (p_reward s'0 +
                   (f s'0 (policy_opt n s'0) n (evaluate_policy_state (policy_opt n) ))
                   (**big_sum (states p_props)
                     (fun s'1 : state_t =>
                      (trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n) ) **) )))
              (actions_nonempty p_props)) s' n)
    ). rewrite Heqf. auto.
    rewrite H0.
    
  
    apply Numerics.plus_elim_l with (- p_reward s).
    repeat rewrite Numerics.plus_assoc.
    rewrite Numerics.plus_neg_l.
    repeat rewrite Numerics.plus_id_l.
    remember ((fun a : action_t =>
         big_sum (states p_props)
           (fun s'0 : state_t =>
            trans_f a s s'0 *
            (p_reward s'0 +
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))) as f.
    assert (
        big_sum (states p_props)
        (fun s' : state_t =>
         trans_f (num_nonempty_argmax (l:=actions p_props) f (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s0 s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s' n) = 

          f (num_nonempty_argmax f (actions_nonempty p_props))).
    { 
      rewrite Heqf.
      apply big_sum_ext; auto.
      unfold eqfun.
      intros.
      assert ((p_reward x +
 big_sum (states p_props)
   (fun s'1 : state_t =>
    trans_f (policy_opt n x) x s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n)) = 
      apply Numerics.mult_simpl_l.
      
 auto.
    rewrite nonempty_argmax_mapmax.
    rewrite Numerics.mult_comm.
    rewrite big_sum_mult_right.
    apply big_sum_ext; auto.
    unfold eqfun.
    intros.
    repeat rewrite <- Numerics.mult_assoc.
    rewrite -> Numerics.mult_comm with discount _.
    repeat rewrite Numerics.mult_assoc.
    remember 

    assert (
      (fun a : action_t =>
      big_sum (states p_props)
        (fun s' : state_t =>
         trans_f a s s' *
         (p_reward s' +
          big_sum (states p_props)
            (fun s'0 : state_t =>
             trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
      =
      (fun a : action_t =>
      big_sum (states p_props)
        (fun s' : state_t =>
         trans_f a s s' *
         (p_reward s' +
          big_sum (states p_props)
            (fun s'0 : state_t =>
             trans_f (policy_opt n s') s' s'0 * discount * policy_opt_eval s'0 n))))
    ).
    { 
      apply functional_extensionality.
      intros.
      apply big_sum_ext; auto.
      unfold eqfun.
      intros.
      assert(
         big_sum (states p_props)
           (fun s'0 : state_t =>
            trans_f (policy_opt n x1) x1 s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n) =
        big_sum (states p_props)
           (fun s'0 : state_t => trans_f (policy_opt n x1) x1 s'0 * discount * policy_opt_eval s'0 n)
      ).
      { apply big_sum_ext; auto. unfold eqfun. intros. rewrite IHn; auto. }
      rewrite H0.
      auto.
    }
    rewrite H0.
    assert (
      (fun s0 : state_t =>
         num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s0 s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n)))))
           = 
        (fun s0 : state_t =>
         num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s0 s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * policy_opt_eval s'0 n)))))
    ).
    {
      apply functional_extensionality.
      intros.
      assert (
        (fun a : action_t =>
           big_sum (states p_props)
             (fun s' : state_t =>
              trans_f a x0 s' *
              (p_reward s' +
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
        =
        (fun a : action_t =>
           big_sum (states p_props)
             (fun s' : state_t =>
              trans_f a x0 s' *
              (p_reward s' +
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f (policy_opt n s') s' s'0 * discount * policy_opt_eval s'0 n))))
      ).
      { 
        apply functional_extensionality. 
        intros. 
        apply big_sum_ext; auto. 
        unfold eqfun. intros.
        assert (
        (fun s'0 : state_t => trans_f (policy_opt n x2) x2 s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n) =
        (fun s'0 : state_t => trans_f (policy_opt n x2) x2 s'0 * discount * policy_opt_eval s'0 n)
      ).
      { apply functional_extensionality. intros. rewrite IHn. auto. }
      rewrite H1.
      auto.
    }
    rewrite H1.
    auto.
  }
  rewrite H1.  

      rewrite 
           (actions_nonempty p_props))
      rewrite IHn; auto.
 rewrite IHn.


    assert (
      trans_f
        (num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
           (actions_nonempty p_props)) s x *
      evaluate_policy_state
        (fun s0 : state_t =>
         num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s0 s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
           (actions_nonempty p_props)) x n =
      trans_f
        (num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t => big_sum (states p_props) (fun s' : state_t => trans_f a s s' * policy_opt_eval s' n))
           (actions_nonempty p_props)) s x * policy_opt_eval x n).
    
    destruct discount_ok.
    destruct H0.
    2: { rewrite <- H0. repeat rewrite Numerics.mult_plus_id_r. auto. }
    
    
    rewrite <- IHn.
    
    Print Forall.

    remember ((num_nonempty_argmax (l:=actions p_props)
        (fun a : action_t =>
         big_sum (states p_props)
           (fun s'0 : state_t =>
            trans_f a s s'0 *
            (p_reward s'0 +
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
        (actions_nonempty p_props))) as f.
    
    
    rewrite <- nonempty_argmax_mapmax.
    rewrite Numerics.plus_le_compat.
    rewrite IHn.
  

  Theorem policy_opt_is_opt_n: forall (p' : policy) (n : nat), policy_leq_n p' (policy_opt n) n.
  Proof.
    intros.
    generalize dependent p'.
    destruct discount_ok.
    induction n.
    { intros. unfold policy_leq_n. intros. simpl. apply Numerics.le_refl. }
    unfold policy_leq_n.
    intros.
    simpl.
    apply Numerics.plus_le_compat.
      apply Numerics.le_refl.
    destruct H0.
    2: { 
      rewrite <- H0.
      apply big_sum_le.
      intros.      
      repeat rewrite Numerics.mult_plus_id_r.
      repeat rewrite Numerics.mult_plus_id_l.
      apply Numerics.le_refl.
    }
    remember (fun s0 => (fun a : action_t =>
         big_sum (states p_props)
           (fun s'0 : state_t =>
            trans_f a s0 s'0 *
            (p_reward s'0 +
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))) as f.
    assert (
         big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s s' * discount *
         evaluate_policy_state
           (fun s0 : state_t =>
            num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t =>
               big_sum (states p_props)
                 (fun s'0 : state_t =>
                  trans_f a s0 s'0 *
                  (p_reward s'0 +
                   big_sum (states p_props)
                     (fun s'1 : state_t =>
                      trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
              (actions_nonempty p_props)) s' n)
        =
        big_sum (states p_props)
          (fun s' : state_t =>
           trans_f
             (num_nonempty_argmax (l:=actions p_props)
                (f s)
                (actions_nonempty p_props)) s s' * discount *
           evaluate_policy_state
             (fun s0 : state_t =>
              num_nonempty_argmax (l:=actions p_props)
                (f s0)
                (actions_nonempty p_props)) s' n)
    ). rewrite Heqf. auto.
    rewrite H2.
    
    rewrite -> num_nonempty_argmax_mult_pos with Nt H action_t (actions p_props) _ discount _; auto.
      

  (**Fixpoint policy_opt  (n : nat) : policy :=
   match n with
   | O =>
      (fun s => num_nonempty_argmax (fun a => big_sum (states p_props) (fun s' => trans_f a s s' * p_reward s')) (actions_nonempty p_props))
   | S n' => fun s => (
      num_nonempty_argmax (fun a => 
          big_sum (states p_props) (fun s' => trans_f a s s' * evaluate_policy_state (policy_opt n') s' n)   
        ) (actions_nonempty p_props)
    )
   end.

  Fixpoint policy_opt_value (n : nat)

  Theorem policy_opt_is_opt_n: forall (p' : policy) (n : nat), policy_leq_n p' (policy_opt n) (S n).
  Proof.
    intros.
    generalize dependent p'.
    induction n.
    {
      unfold policy_leq_n.
      simpl.
      intros.
      apply Numerics.plus_le_compat.
      { apply Numerics.le_refl. }
      destruct discount_ok.
      unfold Numerics.le in H0.
      destruct H0.
      2: {
        rewrite <- H0.
        assert ((fun s' : state_t => trans_f (p' s) s s' * 0 * p_reward s') = 
          (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t => big_sum (states p_props) (fun s'0 : state_t => trans_f a s s'0 * p_reward s'0))
              (actions_nonempty p_props)) s s' * 0 * p_reward s')).
        {
          apply functional_extensionality.
          intros.
          repeat (rewrite Numerics.mult_plus_id_r; rewrite Numerics.mult_plus_id_l).
          auto.
        }
        rewrite <- H2.
        apply Numerics.le_refl.
      }
      rewrite -> num_nonempty_argmax_mult_pos with Nt H action_t (actions p_props) _ discount _; auto.
      assert (
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun n : action_t =>
               big_sum (states p_props) (fun s'0 : state_t => trans_f n s s'0 * p_reward s'0) * discount)
              (actions_nonempty p_props)) s s' * discount * p_reward s') =
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun n : action_t =>
               big_sum (states p_props) (fun s'0 : state_t => trans_f n s s'0 * discount * p_reward s'0))
              (actions_nonempty p_props)) s s' * discount * p_reward s')
      ).
      {
        apply functional_extensionality.
        intros.
        assert(
          (fun n : action_t =>
              big_sum (states p_props) (fun s'0 : state_t => trans_f n s s'0 * p_reward s'0) * discount) =
          (fun n : action_t =>
              big_sum (states p_props) (fun s'0 : state_t => trans_f n s s'0 * discount * p_reward s'0))
        ).
        {
          apply functional_extensionality. intros.
          rewrite big_sum_mult_right.
          assert ( 
              (fun x1 : state_t => trans_f x0 s x1 * p_reward x1 * discount) = 
              (fun x1 : state_t => trans_f x0 s x1 * discount * p_reward x1)
          ).
          { apply functional_extensionality. 
            intros. 
            repeat rewrite <- Numerics.mult_assoc. 
            rewrite -> Numerics.mult_comm with discount (p_reward x1).
            auto.
          }
          rewrite H2.
          auto.
        }
        rewrite H2.
      auto.
    }
    rewrite H2.
    remember (fun n : action_t =>
       big_sum (states p_props) (fun s'0 : state_t => trans_f n s s'0 * discount * p_reward s'0)) as f.
    assert (big_sum (states p_props) (fun s' : state_t => trans_f (p' s) s s' * discount * p_reward s') = f  (p' s)).
    { rewrite Heqf. auto. }
    rewrite H3.
    assert (
      big_sum (states p_props)
      (fun s' : state_t =>
       trans_f (num_nonempty_argmax (l:=actions p_props) f (actions_nonempty p_props)) s s' * discount *
       p_reward s') =
      f (num_nonempty_argmax f (actions_nonempty p_props))).
    { rewrite Heqf. auto. }
    rewrite H4.
    rewrite <- nonempty_argmax_mapmax.
    apply num_nonempty_mapmax_correct.
    destruct (actions_ok p_props).
    apply enum_total.
  }
    destruct discount_ok.
    intros.
    unfold policy_leq_n in *.
    intros.
    simpl (policy_opt n.+1).
    simpl (evaluate_policy_state p' s n.+2).
    assert ( (fun s' =>
              trans_f (p' s) s s' * discount *
              (p_reward s' + big_sum (states p_props) 
                (fun s'0 : state_t => trans_f (p' s') s' s'0 * discount * evaluate_policy_state p' s'0 n))) =
              (fun s' => trans_f (p' s) s s' * discount * evaluate_policy_state p' s' n.+1) ).
    { auto. }
    rewrite H2.
    assert (
      p_reward s + 
      big_sum (states p_props) 
      (fun s' : state_t => trans_f (p' s) s s' * discount * evaluate_policy_state p' s' n.+1) <=
      p_reward s + 
      big_sum (states p_props) 
      (fun s' : state_t => trans_f (p' s) s s' * discount * evaluate_policy_state (policy_opt n) s' n.+1)
    ).
    {
      apply Numerics.plus_le_compat.
        apply Numerics.le_refl.
      apply big_sum_le.
      intros.
      apply Numerics.mult_le_compat_l; auto.
      rewrite <- Numerics.mult_plus_id_l with 0.
      apply Numerics.mult_le_compat; try apply Numerics.le_refl; auto.
      apply (trans_pos (p_props)).
    }
    apply Numerics.le_trans with ( p_reward s +
        big_sum (states p_props)
       (fun s' : state_t => trans_f (p' s) s s' * discount * evaluate_policy_state (policy_opt n) s' n.+1)); auto.
    simpl (evaluate_policy_state _ _ n.+2).
    apply Numerics.plus_le_compat_l.
    







    apply big_sum_le.
    intros.
    
    
    apply functional_extensionality.
    SearchAbout big_sum.















    remember (fun s0 : state_t => (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n)))))
        as f.
    assert( forall (s0 : state_t),
      (fun a : action_t =>
             big_sum (states p_props)
            (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n)))) =
      (f s0)
    ).
    { rewrite Heqf. auto. }
    rewrite H4.
    assert(
          (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) =
        (fun s0 : state_t => num_nonempty_argmax (l:=actions p_props) (f s0) (actions_nonempty p_props))
    ). rewrite Heqf. auto.
    rewrite H5.
    assert ( forall s' : state_t,
      (fun s'0 : state_t =>
       trans_f
         (num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s' s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) s' s'0 * discount *
       evaluate_policy_state
         (fun s0 : state_t => num_nonempty_argmax (l:=actions p_props) (f s0) (actions_nonempty p_props)) s'0
         n) =
        (fun s'0 : state_t =>
       trans_f
         (num_nonempty_argmax (l:=actions p_props)
            (f s'0)
            (actions_nonempty p_props)) s' s'0 * discount *
       evaluate_policy_state
         (fun s0 : state_t => num_nonempty_argmax (l:=actions p_props) (f s0) (actions_nonempty p_props)) s'0
         n) 
    ). intros. rewrite Heqf. auto.
    
    rewrite H5.
    
          



    assert(



       (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props))
       =
        (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            (f s0)
            (actions_nonempty p_props))
       ).  rewrite Heqf. auto.
       
       rewrite H4.
       assert (
         (fun s' : state_t =>
           trans_f
             (num_nonempty_argmax (l:=actions p_props)
                (fun a : action_t =>
                 big_sum (states p_props)
                   (fun s'0 : state_t =>
                    trans_f a s s'0 *
                    (p_reward s'0 +
                     big_sum (states p_props)
                       (fun s'1 : state_t =>
                        trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
                (actions_nonempty p_props)) s s' * discount *
           (p_reward s' +
            big_sum (states p_props)
              (fun s'0 : state_t =>
               trans_f
                 (num_nonempty_argmax (l:=actions p_props)
                    (fun a : action_t =>
                     big_sum (states p_props)
                       (fun s'1 : state_t =>
                        trans_f a s' s'1 *
                        (p_reward s'1 +
                         big_sum (states p_props)
                           (fun s'2 : state_t =>
                            trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
                    (actions_nonempty p_props)) s' s'0 * discount *
               evaluate_policy_state
                 (fun s0 : state_t => num_nonempty_argmax (l:=actions p_props) (f s0) (actions_nonempty p_props)) s'0
                 n))) = 
           (fun s' : state_t =>
           trans_f
             (num_nonempty_argmax (l:=actions p_props)
                (fun a : action_t =>
                 big_sum (states p_props)
                   (fun s'0 : state_t =>
                    trans_f a s s'0 *
                    (p_reward s'0 +
                     big_sum (states p_props)
                       (fun s'1 : state_t =>
                        trans_f (policy_opt n s'0) s'0 s'1 * discount * evaluate_policy_state (policy_opt n) s'1 n))))
                (actions_nonempty p_props)) s s' * discount *
           (p_reward s' +
            big_sum (states p_props)
              (fun s'0 : state_t =>
               trans_f
                 (num_nonempty_argmax (l:=actions p_props)
                    (fun a : action_t =>
                     big_sum (states p_props)
                       (fun s'1 : state_t =>
                        trans_f a s' s'1 *
                        (p_reward s'1 +
                         big_sum (states p_props)
                           (fun s'2 : state_t =>
                            trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
                    (actions_nonempty p_props)) s' s'0 * discount *
               evaluate_policy_state
                 (fun s0 : state_t => num_nonempty_argmax (l:=actions p_props) (f s0) (actions_nonempty p_props)) s'0
                 n)))
       ).
       rewrite H4.
       
       trans_f
         (num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s' s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) s' s'0 * discount *
       evaluate_policy_state
         (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) s'0 n = 0).
        (fun s'0 : state_t =>
       trans_f
         (num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s' s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) s' s'0 * discount *
       evaluate_policy_state
         (fun s0 : state_t =>
          num_nonempty_argmax (l:=actions p_props)
            (fun a : action_t =>
             big_sum (states p_props)
               (fun s'1 : state_t =>
                trans_f a s0 s'1 *
                (p_reward s'1 +
                 big_sum (states p_props)
                   (fun s'2 : state_t =>
                    trans_f (policy_opt n s'1) s'1 s'2 * discount * evaluate_policy_state (policy_opt n) s'2 n))))
            (actions_nonempty p_props)) s'0 n)) = 0
    ).
    
    
    assert (
        evaluate_policy_state
        (fun s0 : state_t =>
         num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s0 s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
           (actions_nonempty p_props)) s n.+2
         =
        evaluate_policy_state
        (fun s0 : state_t =>
         num_nonempty_argmax (l:=actions p_props)
           (fun a : action_t =>
            big_sum (states p_props)
              (fun s' : state_t =>
               trans_f a s0 s' *
               (p_reward s' +
                big_sum (states p_props)
                  (fun s'0 : state_t =>
                   trans_f (policy_opt n s') s' s'0 * discount * evaluate_policy_state (policy_opt n) s'0 n))))
           (actions_nonempty p_props)) s n.+2
        
    )
    unfold Numerics.le.
    right.
    simpl.
    auto.
    
      auto.


        SearchAbout Numerics.le. 
    SearchAbout big_sum.

      Print evaluate_policy_state.
      fold (evalate_policy_state p' s       
      assert (forall s'0: state_t, evaluate_policy_state p' s'0 n <= evaluate_policy_state (policy_opt n) s'0 n).
      {
        intros.
        
        
        simpl.
      { 
        intros.
        destruct n0.
         apply Numerics.le_refl.
        simpl.
 apply H2.
      remember (fun a : action_t => big_sum (states p_props)
        (fun s' : state_t => trans_f a s s' * discount * evaluate_policy_state p'0 s' n0)
      
      
    2:{
      induction n.
      apply H0.
      destruct n.
      intros.
      apply H1 with p'.
      auto.
      apply IHn.
      intros.
      apply H1 with p'.
      auto.
      auto.
    }
      simpl.
      intros.
  
    
    intros.
    simpl.
    unfold policy_leq_n in *.
    intros.
    
    rewrite H0.

)
    simpl in *.
    
    
    rewrite IHn.
    
      auto.
      2: { rewrite H4. rewrite <- nonempty_argmax_mapmax.
      

 rewrite Heqf.
      auto.
        rewrite H2.
        auto.

          assert( 

 apply functional_extensionality. intros. rewrite <- plus_assoc.
        rewrite big_sum_mult_right.
        auto.

      rewrite <- nonempty_argmax_mapmax.
      
      2: { apply Numerics.le_lt_weak; auto.
      assert(
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t => big_sum (states p_props) (fun s'0 : state_t => trans_f a s s'0 * p_reward s'0))
              (actions_nonempty p_props)) s s' * discount * p_reward s') =
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t => big_sum (states p_props) (fun s'0 : state_t => trans_f a s s'0 * p_reward s'0))
              (actions_nonempty p_props)) s s'  * p_reward s' )
        ).
        {
          apply functional_extensionality.
          intros.
          rewrite <- Numerics.mult_assoc with _ (p_reward x) discount.
          rewrite -> Numerics.mult_comm with (p_reward x) discount.
          rewrite Numerics.mult_assoc.
          auto.
        }
        rewrite H0.

        
      assert (
        big_sum (states p_props)
        (fun s' : state_t =>
         trans_f
           (num_nonempty_argmax (l:=actions p_props)
              (fun a : action_t => big_sum (states p_props) (fun s'0 : state_t => trans_f a s s'0 *  p_reward s'0))
              (actions_nonempty p_props)) s s' * discount * p_reward s')
        =
        num_nonempty_mapmax 
          (fun a : action_t =>
            (big_sum (states p_props) (fun s' : state_t => trans_f
               a s s' * p_reward s'))) (actions_nonempty p_props)
           
        ).
        {
          assert (num_nonempty_mapmax 
          (fun a : action_t =>
            (big_sum (states p_props) (fun s' : state_t => trans_f
               a s s' * p_reward s'))) (actions_nonempty p_props)
           =
          num_nonempty_mapmax 
          (fun a : action_t =>
            (big_sum (states p_props) (fun s' : state_t => trans_f
               a s s' * p_reward s' * discount))) (actions_nonempty p_props)
           
          ).
          {
            (**assert (
              (fun a : action_t => big_sum (states p_props) 
                  (fun s' : state_t => trans_f a s s' * p_reward s' * discount)) =
              (fun a : action_t => big_sum (states p_props) 
                  (fun s' : state_t => (fun s'' => trans_f a s s'' * p_reward s'') s' * discount))
              
            ).
            { apply functional_extensionality. auto. }
            rewrite H0.
            
        )). **)
          rewrite nonempty_argmax_mapmax.
          apply 
          rewrite -> num_nonempty_argmax_mult_pos with discount.


          apply big_sum_ext; auto.
        }
        rewrite H0.
          unfold eqfun.
          intros.
          auto.
        
      rewrite <- Heqf.
      
      
      remember ((num_nonempty_argmax (l:=actions p_props)
        (fun a : action_t => big_sum (states p_props) (fun s'0 : state_t => trans_f a s s'0 * p_reward s'0))
        (actions_nonempty p_props))) as a.
      induct
      apply big_sum_le.
      intros.
      
      **)
      
    

  (**

  Definition policy_leq_sum  (pol1 pol2 : policy) : Prop :=
  exists (n0 : nat), forall (m : nat), (n0 <= m)%nat -> evaluate_policy_sum pol1 m <= evaluate_policy_sum pol2 m.

  Lemma policy_leq_sum_trans: forall (pol1 pol2 pol3 : policy), policy_leq_sum pol1 pol2 -> policy_leq_sum pol2 pol3 -> policy_leq_sum pol1 pol3.
  Proof.
    unfold policy_leq_sum.
    intros.
    destruct H0.
    destruct H1.
    exists (Nat.max x x0).
    intros.
    apply Numerics.le_trans with (evaluate_policy_sum pol2 m).
    {
      apply H0.
      apply Nat.max_lub_l with x0; auto.
    }
    apply H1.
    apply Nat.max_lub_r with x; auto.
  Qed.

  Lemma poliy_leq_sum_asymm: forall (pol1 pol2 : policy) policy_leq_sum pol1 pol2 -> policy_leq_sum pol2 pol1
  **)



    

End mdp_numeric.

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
