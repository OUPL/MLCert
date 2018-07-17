Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import FunctionalExtensionality.

Class Monad (M:Type->Type) :=
  mkMonad {
      ret : forall a (x:a), M a;
      bind : forall a b (m:M a) (f:a->M b), M b;
      bind_assoc : forall a b c (m:M a) (f:a->M b) (g:b->M c),
          bind m (fun a => bind (f a) g) =
          bind (bind m f) g
    }.

Notation "x <-- e1 ; e2" := (bind e1 (fun x => e2)) 
  (at level 100, right associativity, only parsing).

Section foldrM.
  Context {M} `{Monad M}.

  Fixpoint foldrM (T R : Type) (f:T -> R -> M R) (z0:R) (s:seq T) : M R :=
    match s with
    | [::] => ret z0
    | x :: s' => r <-- foldrM f z0 s'; f x r
    end.
End foldrM.        

Section mapM.
  Context {M} `{Monad M}.

  Fixpoint mapM (T R : Type) (f:T -> M R) (s:seq T) : M (seq R) :=
    match s with
    | [::] => ret [::]
    | x :: s' => x' <-- f x; r' <-- mapM f s'; ret [:: x' & r'] 
    end.
End mapM.        

Section IdMonad.
  Definition Id (a:Type) : Type := a.
  Definition Iret a (x:a) : Id a := x.
  Definition Ibind a b (m:Id a) (f:a -> Id b) : Id b := f m.
  Global Program Instance IdMonad : Monad Id := @mkMonad _ Iret Ibind _.
End IdMonad.

Section StateMonadTransformer.
  Context {M} `{Monad M}.
  Variable state:Type.
  
  Definition StateT (a:Type) : Type := state -> M (a * state).

  Definition Sret a (x:a) : StateT a := fun s => ret (x,s).

  Definition Sbind a b (m:StateT a) (f:a -> StateT b) : StateT b :=
    fun s:state => xs' <-- m s; let: (x,s') := xs' in f x s'.

  Global Program Instance StateMonad : Monad StateT := @mkMonad _ Sret Sbind _.
  Next Obligation.
    rewrite /Sbind; apply: functional_extensionality => x.
    by rewrite -bind_assoc; f_equal; apply: functional_extensionality => [][]z w.
  Qed.
End StateMonadTransformer.

Definition State := StateT (M:=Id).

Section StateMonadMethods.
  Variable state:Type.

  Definition get : State state state := fun s => (s,s).

  Definition modify (f:state -> state) : State state unit :=
    fun s => (tt, f s).

  Definition runState a (m:State state a) (s:state) : a :=
    let: (x,s') := m s in x.
End StateMonadMethods.  

Section ContMonad.
  Variable r:Type.

  Definition Cont (a:Type) : Type := (a -> r) -> r.

  Definition Cret a (x:a) : Cont a := fun k => k x.
  
  Definition Cbind a b (m:Cont a) (f:a->Cont b) : Cont b :=
    fun k => m (fun x => f x k).

  Global Program Instance ContMonad : Monad Cont := @mkMonad _ Cret Cbind _.
End ContMonad.

Class Foldable (t T:Type) : Type :=
  mkFoldable {
      foldable_foldM {M} `{Monad M} (R:Type) : (T -> R -> M R) -> R -> t -> M R;      
      foldable_mapM {M} `{Monad M} : (T -> M T) -> t -> M t
    }.

Section list_Foldable.
  Variable T:Type.

  Fixpoint list_foldM M `(Monad M) (R:Type) (f:T->R->M R) (r0:R) (l:list T) : M R :=
    match l with
    | nil => ret r0
    | cons x l' => r' <-- f x r0; list_foldM _ f r' l'
    end.

  Fixpoint list_mapM M `(Monad M) (f:T->M T) (l:list T) : M (list T) :=
    match l with
    | nil => ret nil
    | cons x l' => x' <-- f x; l'' <-- list_mapM _ f l'; ret (cons x' l'')
    end.

  Global Instance list_Foldable : Foldable (list T) T :=
    mkFoldable list_foldM list_mapM.
End list_Foldable.  