Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Class Monad (M:Type->Type) :=
  mkMonad {
      ret : forall a (x:a), M a;
      bind : forall a b (m:M a) (f:a -> M b), M b
    }.

Notation "x <-- e1 ; e2" := (bind e1 (fun x => e2)) 
  (at level 100, right associativity).

Section StateMonad.
  Variable state:Type.
  
  Definition State (a:Type) : Type := state -> a * state.

  Definition Sret a (x:a) : State a := fun s => (x,s).

  Definition Sbind a b (m:State a) (f:a -> State b) : State b :=
    fun s:state => let: (x,s') := m s in f x s'.

  Global Instance StateMonad : Monad State := mkMonad Sret Sbind.  
End StateMonad.

Section StateMonadMethods.
  Variable state:Type.

  Definition get : State state state := fun s => (s,s).

  Definition modify (f:state -> state) : State state unit :=
    fun s => (tt, f s).
End StateMonadMethods.  

Section ContMonad.
  Variable r:Type.

  Definition Cont (a:Type) : Type := (a -> r) -> r.

  Definition Cret a (x:a) : Cont a := fun k => k x.
  
  Definition Cbind a b (m:Cont a) (f:a->Cont b) : Cont b :=
    fun k => m (fun x => f x k).

  Global Instance ContMonad : Monad Cont := mkMonad Cret Cbind.
End ContMonad.
