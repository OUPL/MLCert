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

(**Open Scope f32_scope.**)


Require Import OUVerT.numerics.
Require Import OUVerT.generalized_bigops.
Require Import OUVerT.dyadic.
Require Import ProofIrrelevance.



Delimit Scope Numeric_scope with Num.
Local Open Scope Num.
Section mdp_numeric. 
  Context (Nt:Type) `{Numerics.Numeric Nt}.
  Record mdp : Type := mdp_mk {
    state : Type;
    action : Type;
    states : list state;
    actions : list action;
    trans : action -> state -> state -> Nt;
    reward : state -> Nt;
    discount : Nt;
    trans_sum1: forall (s : state) (a : action), 
        List.In s states -> big_sum states (fun s' => trans a s s') = Numerics.mult_id;
    discount_ok : (Numerics.plus_id < discount /\ discount < Numerics.mult_id)%Num;
    states_nonempty : (0 <> length states)%nat;
    actions_nonempty : (0 <> length actions)%nat;
  }.

  Definition value_func (p : mdp) := state p -> Nt.
  Definition policy (p : mdp) := state p -> action p.


  Definition value_func0 (p : mdp) := (fun (x : state p) => Numerics.plus_id).

  Definition discounted_reward (p : mdp) (v : value_func p) (s : (state p)) (a : (action p)) : Nt :=
    (reward p) s + big_sum (states p) (fun  s' =>  ((trans p) a s s') * (discount p) * (v s'))%Num.


  Definition value_iteration_step (p : mdp) (v : value_func p) : value_func p := 
    (fun (s : state p) => 
      Numerics.list_max_default (seq.map (fun a => discounted_reward p v s a) (actions p)) Numerics.plus_id
  ).

  Fixpoint value_iteration_rec (p : mdp) (v : value_func p) (n : nat):=
  match n with
  | O => v
  | S n' => value_iteration_rec p (value_iteration_step p v) n'
  end.

  Definition value_iteration (p : mdp) (n : nat) :=
    value_iteration_rec p (value_func0 p) n.


  Fixpoint evaluate_policy_state (p : mdp) (pol : policy p) (s : state p) (i : nat): Nt :=
  match i with 
  | O => (reward p) s
  | S i' => (reward p) s +
        Numerics.list_max_default
        (seq.map 
          (fun a => (big_sum (states p)  (fun s' =>  ((trans p) a s s') * (discount p) * (evaluate_policy_state p pol s' i'))))
          (actions p))
        Numerics.plus_id
  end.

  Lemma exists_action: forall (p : mdp), exists a : (action p), In a (actions p).
  Proof.
    intros.
    destruct (actions p) eqn:e.
    {
      destruct p; simpl in *;
      rewrite e in actions_nonempty0;
      exfalso; auto.
    }
    exists a.
    apply in_eq.
  Qed.
  
  Definition value_diff (p : mdp) (v1 v2 : value_func p) : value_func p :=
  (fun s => v1 s + - v2 s).

  Definition value_dist (p : mdp) (v1 v2 : value_func p) : Nt :=
  Numerics.list_max_default  (seq.map (fun s => Numerics.abs ((value_diff p v1 v2) s) ) (states p) )Numerics.plus_id.

  
  Definition head_action (p : mdp) : (action p).
  destruct p.
  simpl in *.
  destruct actions0.
  { simpl in *. exfalso. auto. }
  exact a.
  Defined.


  Lemma head_action_correct: forall (p : mdp), Some (head_action p) = head (actions p).
  Proof.
    intros.
    destruct p.
    destruct actions0.
    simpl. 
    { exfalso. auto. }
    auto.
  Qed.
 
  Definition value_func_policy (p : mdp) (v: value_func p) : policy p :=
  (fun s => Numerics.argmax_default (actions p) (fun a => discounted_reward p v s a) (head_action p)).
  
  
  Definition evaluate_policy_all (p : mdp) (pol : policy p) (n : nat) : Nt :=
  big_sum (states p) (fun s => evaluate_policy_state p pol s n). 

  Definition policy_value_leq (p : mdp) (pol1 pol2 : policy p) : Prop :=
  exists n0 : nat, forall m : nat, (n0 <= m)%nat -> evaluate_policy_all p pol1 m <= evaluate_policy_all p pol2 m.

  Theorem value_iteration_contraction:  forall (p : mdp) (v1 v2 : value_func p),
  value_dist p (value_iteration_step p v1) (value_iteration_step p v1) 
      <= (discount p) * (value_dist p v1 v2).
  Proof.
    intros.
    unfold value_dist.
    unfold value_diff.
    unfold value_iteration_step.
    unfold discounted_reward.
    unfold value_func in v1,v2.
    destruct p.
    simpl in *.
  Admitted.
    
    

  Theorem value_iteration_monotonic: forall (p : mdp) (v : value_func p), 
      policy_value_leq p (value_func_policy p v) (value_func_policy p (value_iteration_step p v)).
  Admitted.

  Theorem policy_max: forall (p : mdp), exists x : Nt, 
    (forall (pol : policy p) (n : nat), evaluate_policy_all p pol n <= x).
  Admitted.


  Theorem value_iteration_converge: forall (p : mdp) (v : value_func p) (eps : Nt), exists n0 : nat, 
       forall (n m : nat), Numerics.abs ( value_dist p (value_iteration_rec p v n) (value_iteration_rec p v m)  ) < eps.
  Admitted.
    

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
