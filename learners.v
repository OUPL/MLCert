Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import Extraction.

Require Import MLCert.float32.

Module Learner.
  Record t (A B hypers params : Type) :=
    mk { predict : hypers -> params -> A -> B;
         update : hypers -> A*B -> params -> params }.
End Learner.

Section state_monad.
  Variable state : Type.
  Definition State (T : Type) : Type := state -> state*T.
  Definition ret T (t:T) : State T := fun s => (s,t).
  Definition bind T U (m:State T) (f:T -> State U) : State U :=
    fun s => let: (s',t) := m s in f t s'.
  Definition modify (f:state -> state) : State unit := fun s => (f s, tt).
End state_monad.        

Section Exp.
  Variables A B hypers params : Type.
  Variable learner : Learner.t A B hypers params.
  Variable h : hypers.
  Variable sampler_state : Type.
  Variable sample : State sampler_state (A*B).

  Inductive exp : Type -> Type :=
  | Sample : exp (A*B)
  | Update : A*B -> exp unit
  | Iter : nat -> exp unit -> exp unit
  | Bind : forall t1 t2, exp t1 -> (t1 -> exp t2) -> exp t2.
  
  Definition lift_left state1 state2 T (m:State state1 T)
    : State (state1*state2) T :=
    fun s => let: (s1,s2) := s in
             let: (s1',t) := m s1 in
             ((s1',s2), t).

  Definition lift_unit state (m:State state unit) : state*unit -> state*unit :=
    fun s => let: (s1,_) := s in m s1.
  
  Fixpoint run T (e : exp T) : State (sampler_state*params) T :=
    match e with
    | Sample => lift_left sample
    | Update ab => modify (fun s => let: (r,p) := s in (r,Learner.update learner h ab p))
    | Iter n e1 => fun s => Nat.iter n (lift_unit (run e1)) (s, tt)
    | Bind _ _ e1 f2 => bind (run e1) (fun v1 => run (f2 v1))                        
    end.
End Exp.

Notation "'sample'" := (@Sample _ _).
Notation "'upd'" := (@Update _ _).
Notation "x <-- e1 ; e2" := (Bind e1 (fun x => e2)) (at level 100).
Notation "'iter'" := (Iter).

Section learning.
  Variables A B hypers params : Type.
  Variable learner : Learner.t A B hypers params.
  Variable h : hypers.
  Variable epochs : nat.

  Definition train : exp A B unit := iter epochs (ab <-- sample; upd ab).

  Definition go (sampler_state:Type) (sampler:State sampler_state (A*B)) :=
    run learner h sampler train.
End learning.
