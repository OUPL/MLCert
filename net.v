Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List Arith NArith String. Import ListNotations.
Require Import ProofIrrelevance.

Require Import dyadic numerics vector compile.

Definition weight := D.

(* the type of nets *)

Module Net (D : BOUND) (T : PAYLOAD).
  (* D = dimensionality 
     T = the type of network inputs *)

  Module Env := Vector D T.
  (* An environment maps variables Ix.t to values of type T *)
  Definition var := Env.Ix.t.
  
  Inductive t : Type :=
  | NIn : var -> t
  | NReLU : t -> t
  | NComb : list (weight * t) -> t.
End Net.

(* value ranges (a symbolic instantiation) *)

Local Open Scope D_scope.

Definition Dmin (d1 d2 : D) : D :=
  if Dlt_bool d1 d2 then d1 else d2.

Inductive Dintv : Type :=
| Dtop : Dintv (*[-inf, +inf]*)
| Dbot : Dintv (*[+inf, -inf]*)
| Dneg : D -> Dintv (*a negative halfspace [-inf, hi]*)
| Dpos : D -> Dintv (*a positive halfspace [lo, +inf]*)
| Dlh : D -> D -> Dintv. (*[lo,hi]*)

Definition Dmeet (d1 d2 : Dintv) : Dintv :=
  match d1, d2 with
  | Dtop, _ => d2
  | _, Dtop => d1
  | Dbot, _ => Dbot
  | _, Dbot => Dbot

  | Dneg h1, Dneg h2 => Dneg (Dmin h1 h2)
  | Dneg h1, Dpos l2 => Dlh l2 h1
  | Dneg h1, Dlh l2 h2 => Dlh l2 (Dmin h1 h2)

  | Dpos l1, Dneg h2 => Dlh l1 h2
  | Dpos l1, Dpos l2 => Dpos (Dmax l1 l2)
  | Dpos l1, Dlh l2 h2 => Dlh (Dmax l1 l2) h2

  | Dlh l1 h1, Dneg h2 => Dlh l1 (Dmin h1 h2)
  | Dlh l1 h1, Dpos l2 => Dlh (Dmax l1 l2) h1
  | Dlh l1 h1, Dlh l2 h2 => Dlh (Dmax l1 l2) (Dmin h1 h2)
  end.

Definition Djoin (d1 d2 : Dintv) : Dintv :=
  match d1, d2 with
  | Dtop, _ => Dtop
  | _, Dtop => Dtop
  | Dbot, _ => d2
  | _, Dbot => d1

  | Dneg h1, Dneg h2 => Dneg (Dmax h1 h2)
  | Dneg h1, Dpos l2 => Dlh l2 h1
  | Dneg h1, Dlh _ h2 => Dneg (Dmax h1 h2)

  | Dpos l1, Dneg h2 => Dlh l1 h2
  | Dpos l1, Dpos l2 => Dpos (Dmin l1 l2)
  | Dpos l1, Dlh l2 _ => Dpos (Dmin l1 l2)

  | Dlh l1 h1, Dneg h2 => Dneg (Dmax h1 h2)
  | Dlh l1 h1, Dpos l2 => Dpos (Dmin l1 l2)
  | Dlh l1 h1, Dlh l2 h2 => Dlh (Dmin l1 l2) (Dmax h1 h2)
  end.

Definition Drelu (d : Dintv) : Dintv :=
  match d with
  | Dtop => Dpos 0
  | Dbot => Dbot
  | Dneg h => Dlh 0 (Dmax 0 h)
  | Dpos l => Dpos (Dmax 0 l)
  | Dlh l h => Dlh (Dmax 0 l) (Dmax 0 h)
  end.

Definition Dadd (d1 d2 : Dintv) : Dintv :=
  match d1, d2 with
  | Dtop, _ => Dtop
  | _, Dtop => Dtop
  | Dbot, _ => Dbot
  | _, Dbot => Dbot
                 
  | Dneg h1, Dneg h2 => Dneg (h1 + h2)
  | Dneg h1, Dpos l2 => Dtop
  | Dneg h1, Dlh l2 h2 => Dneg (h1 + h2)

  | Dpos l1, Dneg h2 => Dtop
  | Dpos l1, Dpos l2 => Dpos (l1 + l2)
  | Dpos l1, Dlh l2 h2 => Dpos (l1 + l2)

  | Dlh l1 h1, Dneg h2 => Dneg (h1 + h2)
  | Dlh l1 h1, Dpos l2 => Dpos (l1 + l2)
  | Dlh l1 h1, Dlh l2 h2 => Dlh (l1 + l2) (h1 + h2)
  end.

Definition Dinv (d : Dintv) : Dintv :=
  match d with
  | Dbot => Dbot
  | Dtop => Dtop
  | Dneg h => Dpos h
  | Dpos l => Dneg l
  | Dlh l h => Dlh h l
  end.

Definition Dmult_aux (c : D) (d : Dintv) : Dintv :=
  match d with
  | Dbot => Dbot
  | Dtop => Dtop
  | Dneg h => Dneg (c * h)
  | Dpos l => Dpos (c * l)
  | Dlh l h => Dlh (c * l) (c * h)
  end.

Definition Dmult (c : D) (d : Dintv) : Dintv :=
  let d' := Dmult_aux c d in
  if Dlt_bool c 0 then Dinv d' else d'.

Definition Dreduce (d : Dintv) : Dintv :=
  match d with
  | Dbot => Dbot
  | Dtop => Dtop
  | Dneg h => Dneg (Dred h)
  | Dpos l => Dpos (Dred l)
  | Dlh l h =>
    if Dlt_bool h l then Dbot
    else Dlh (Dred l) (Dred h)
  end.

Class domain (T : Type) :=
  mkDomain {
      dzero_inf : T;
      dinf_zero : T;
      dmeet : T -> T -> T;
      djoin : T -> T -> T;
      drelu : T -> T;
      dadd : T -> T -> T;
      dmult : D -> T -> T;
      dred : T -> T;
    }.

Instance domain_Dpair : domain Dintv :=
  mkDomain (Dpos 0) (Dneg 0) Dmeet Djoin Drelu Dadd Dmult Dreduce.

(* symbolic execution *)

Fixpoint seval_comb {T} `{domain T} (acc : T) (l : list (weight * T)) : T :=
  match l with
  | (w, t) :: l' => seval_comb (dadd (dmult w t) acc) l'
  | [] => acc
  end.

Module NetEval (D : BOUND) (T : PAYLOAD).
  Module NET := Net D T. Include NET.
           
  Fixpoint seval `{domain T.t} (rho : NET.Env.t) (n : NET.t) : T.t :=
    match n with
    | NIn x => dred (NET.Env.get x rho)
    | NReLU n' => dred (drelu (seval rho n'))
    | NComb l =>
      let l' := map (fun p => (fst p, seval rho (snd p))) l
      in dred (seval_comb (dmeet dzero_inf dinf_zero) l')
    end.
End NetEval.

(* symbolic out *)

Module DIntvPayload <: PAYLOAD.
  Definition t := Dintv.
  Definition t0 := Dbot.
  Definition eq0 (x : t) :=
    match x with
    | Dbot => true
    | _ => false
    end.
  Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
  Proof. rewrite /t0; case: x => /=; try solve[constructor => //]. Qed.
  Definition u := t.
  Definition u_of_t (x : t) : u := x.
  Definition t_of_u (y : u) : t := y.
  Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
  Proof. by []. Qed.
End DIntvPayload.

Module Test1Symbolic.
Module Test1Bound <: BOUND.
  Definition n:nat := 1.
  Lemma n_gt0 : (0 < n)%nat. by []. Qed.
End Test1Bound.
Module Test1 := NetEval Test1Bound DIntvPayload. Import Test1. Import NET.
Program Definition x : var := @Env.Ix.mk 0 _.
Definition rho : Env.t := Env.of_fun (fun _ => Dlh 0 1).
Definition v11 := NIn x.
(*Compute seval rho v11.*)
Definition v21b := NComb [(1,v11)].
(*Compute seval rho v21b.*)
Definition v22b := NComb [(-(1),v11)].
(*Compute seval rho v22b.*)
Definition v21f := NReLU v21b.
(*Compute seval rho v21f.*)
Definition v22f := NReLU v22b.
(*Compute seval rho v22f.*)
Definition v31 := NComb [(1,v21f); (1,v22f)].
(*Compute seval rho v31.*)
End Test1Symbolic.

Instance domain_D : domain D :=
  mkDomain
    0 0 (fun x _ => x) (fun x _ => x)
    (fun x => Dmax 0 x)
    dyadic.Dadd
    dyadic.Dmult
    Dred.

Module Test1Concrete.
Module Test1Bound <: BOUND.
  Definition n:nat := 1.
  Lemma n_gt0 : (0 < n)%nat. by []. Qed.
End Test1Bound.
Module Test1 := NetEval Test1Bound DPayload. Import Test1. Import NET.
Program Definition x : var := @Env.Ix.mk 0 _.
Definition rho : Env.t := Env.of_fun (fun _ => DRed.build (Dmake 8 1)).
Definition v11' := NIn x.
Definition v21b' := NComb [(1,v11')].
Definition v22b' := NComb [(-(1),v11')].
Definition v21f' := NReLU v21b'.
Definition v22f' := NReLU v22b'.
Definition v31' := NComb [(1,v21f'); (1,v22f')].
End Test1Concrete.

(* forests of nets *)

Module Forest (D OUT : BOUND) (T : PAYLOAD).
  (* D = dimensionality of input space 
     OUT = number of outputs 
     T = payload *)
  Module NET := NetEval D T. Import NET.
  Module NETPayload <: PAYLOAD.
    Definition t := NET.t.
    Definition i0 := @NET.Env.Ix.mk 0 D.n_gt0.
    Definition t0 := NET.NIn i0.
    Definition eq0 (x : t) :=
      match x with
      | NIn y => match y with
                 | NET.Env.Ix.mk z _ => 
                     if Nat.eq_dec z 0 then true else false
                 end
      | _ => false
      end.
    Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
    Proof.
      rewrite /t0; case: x => /=.
      { case => /= x pf; rewrite /i0.
        destruct (Nat.eq_dec x 0) eqn:H.
        { subst; constructor; f_equal. admit. }
        { admit. }}
      { move => l; constructor => //. }
      move => l; constructor => //.
    Admitted.
    Definition u := t.
    Definition u_of_t (x : t) : u := x.
    Definition t_of_u (y : u) : t := y.
    Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
    Proof. by []. Qed.
  End NETPayload.

  (* a forest is an OUT-vector of NETs *)
  Module Forest := Vector OUT NETPayload.
  Module Output := Vector OUT T.

  (* execute a forest *)
  Definition Output_ix_to_ix (x : Output.Ix.t) : Forest.Ix.t :=
    match x with
    | Output.Ix.mk _ pf => Forest.Ix.mk pf
    end.
  Coercion Output_ix_to_ix : Output.Ix.t >-> Forest.Ix.t.

  Definition seval `{domain T.t} 
      (rho : Env.t) (f : Forest.t) : Output.t :=
    Output.of_fun (fun ix => Forest.NET.seval rho (Forest.get ix f)).
End Forest.