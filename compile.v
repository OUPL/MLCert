Set Implicit Arguments.
Unset Strict Implicit.

Require Import ProofIrrelevance.
Require Import QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema numerics dyadic strings.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Module OrdNat
  <: OrderedType.OrderedType.
      Definition t := N.t.
      Definition eq := N.eq.
      Definition lt := N.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. apply: N.eq_sym. Qed.                                      
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. apply: N.lt_trans. Qed.                                           
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. move=> x y H H2; rewrite /eq /N.eq in H2; subst x.
             apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof. move=> x y; case H: (N.eq_dec x y).
             { by subst x; apply: OrderedType.EQ. }
             case H2: (N.ltb x y).
             { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
             apply: OrderedType.GT.
             have H3: N.le y x.
             { by rewrite -N.ltb_ge H2. }
             move: H3; rewrite N.lt_eq_cases; case => //.
             by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. apply: N.eq_dec. Qed.
End OrdNat.
      
Module M := Make OrdNat. (* The type of shared states *)
Module MFacts := Facts M.
Module MProps := Properties M.

(** OrdNatDep: A computational analogue of 'I_n *)

Module Type BOUND.
  Parameter n : nat.
  Parameter n_gt0 : (0 < n)%nat.
End BOUND.

Module OrdNatDep (B : BOUND)
  <: OrderedType.OrderedType.
      Notation n := B.n.
      Record t' : Type :=
        mk { val :> N.t;
             pf : (N.to_nat val < n)%nat }.
      Definition t := t'.
      Definition eq (x y : t) := N.eq (val x) (val y).
      Definition lt (x y : t) := N.lt (val x) (val y).
      Lemma eq_refl : forall x : t, eq x x.
      Proof. case => x pf; apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. case => x pf; case => y pf'; apply: N.eq_sym. Qed.   
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. case => x pf; case => y pf'; case => z pf''; apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. case => x pf; case => y pf'; case => z pf''; apply: N.lt_trans. Qed.        
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. case => x pf; case => y pf' H H2; rewrite /eq /N.eq in H2.
             rewrite /lt H2 in H; apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof.
        case => x pf; case => y pf'; case H: (N.eq_dec x y).
        { by subst x; apply: OrderedType.EQ. }
        case H2: (N.ltb x y).
        { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
        apply: OrderedType.GT.
        have H3: N.le y x.
        { by rewrite -N.ltb_ge H2. }
        move: H3; rewrite N.lt_eq_cases; case => //.
        by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. case => x pf; case => y pf'; apply: N.eq_dec. Qed.
End OrdNatDep.

Class Enumerable (T : Type) :=
  enumerable_fun : list T.
Notation "'enumerate' T" := (@enumerable_fun T _) (at level 30).

Class Enum_ok A `{Enumerable A} : Type :=
  mkEnum_ok { 
      enum_nodup : NoDupA (fun x : A => [eta eq x]) (enumerate A);
      enum_total : forall a : A, In a (enumerate A)
    }.

Instance prodEnumerableInstance (aT bT : Type)
         (enumerableA : Enumerable aT)
         (enumerableB : Enumerable bT)
  : Enumerable (aT*bT) :=
  List.list_prod (enumerate aT) (enumerate bT).

Class Eq (A : Type) : Type :=
  decEq : A -> A -> Prop.

Class Eq_Dec (A : Type) (eq : Eq A) : Type :=
  isDec : forall x y : A,  {eq x y} + {~ eq x y}.

Class Eq_Refl (A : Type) (eq :Eq A) : Type :=
  isRefl : forall x : A, eq x x.

Instance eqProd
      (A B: Type) (eqA : Eq A) (eqB : Eq B)
  : Eq (A*B)%type :=
    fun p1 p2 =>
    match p1, p2 with
    | (a1, b1), (a2, b2) => (eqA a1 a2) /\ (eqB b1 b2)
    end. 
