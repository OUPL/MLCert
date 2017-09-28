Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith. Import ListNotations.

Require Import dyadic numerics vector compile.

Definition weight := D.

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

Inductive net {T} `{domain T} : Type :=
| NIn : forall t : T,  net
| NReLU : net -> net
| NComb : list (weight * net) -> net.

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

Instance domain_Dpair : domain Dintv :=
  mkDomain (Dpos 0) (Dneg 0) Dmeet Djoin Drelu Dadd Dmult Dreduce.

(* symbolic execution *)

Fixpoint seval_comb {T} `{domain T} (acc : T) (l : list (weight * T)) : T :=
  match l with
  | (w, t) :: l' => seval_comb (dadd (dmult w t) acc) l'
  | [] => acc
  end.

Fixpoint seval {T} `{domain T} (n : net) : T :=
  match n with
  | NIn t => dred t
  | NReLU n' => dred (drelu (seval n'))
  | NComb l =>
    let l' := map (fun p => (fst p, seval (snd p))) l
    in dred (seval_comb (dmeet dzero_inf dinf_zero) l')
  end.

Definition v11 := NIn (Dlh 0 1).
Compute seval v11.
Definition v21b := NComb [(1,v11)].
Compute seval v21b.
Definition v22b := NComb [(-(1),v11)].
Compute seval v22b.
Definition v21f := NReLU v21b.
Compute seval v21f.
Definition v22f := NReLU v22b.
Compute seval v22f.
Definition v31 := NComb [(1,v21f); (1,v22f)].
Compute seval v31.

(* concrete execution *)

Instance domain_D : domain D :=
  mkDomain
    0 0 (fun x _ => x) (fun x _ => x)
    (fun x => Dmax 0 x)
    dyadic.Dadd
    dyadic.Dmult
    Dred.

Definition eval (n : net) : D := seval n.

Definition v11' := NIn (Dmake 8 1).
Compute seval v11'.
Definition v21b' := NComb [(1,v11')].
Compute seval v21b'.
Definition v22b' := NComb [(-(1),v11')].
Compute seval v22b'.
Definition v21f' := NReLU v21b'.
Compute seval v21f'.
Definition v22f' := NReLU v22b'.
Compute seval v22f'.
Definition v31' := NComb [(1,v21f'); (1,v22f')].
Compute seval v31'.

(* forests of nets *)

(* concrete out *)

(* DPayload *)

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

(* concrete in *)

Module DNetPayload <: PAYLOAD.
  Definition t := @net D _.
  Definition t0 := NIn D0.
  Definition eq0 (x : t) :=
    match x with
    | NIn d => if Deq_dec d 0 then true else false
    | _ => false
    end.
  Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
  Proof.
    rewrite /t0; case: x => /=.
    { move => x; case: (Deq_dec x 0) => /=.
      { move => ->; constructor => //. }
      move => H; constructor => // H2; apply: H; inversion H2 => //. }
    { move => l; constructor => //. }
    move => l; constructor => //.    
  Qed.
  Definition u := t.
  Definition u_of_t (x : t) : u := x.
  Definition t_of_u (y : u) : t := y.
  Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
  Proof. by []. Qed.
End DNetPayload.

(* symbolic in *) 

Module DIntvNetPayload <: PAYLOAD.
  Definition t := @net Dintv _.
  Definition t0 := NIn Dbot.
  Definition eq0 (x : t) :=
    match x with
    | NIn Dbot => true
    | _ => false
    end.
  Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
  Proof.
    rewrite /t0; case: x => /=.
    { case; constructor => //; inversion 1. }
    { move => n; constructor => //. }
    move => l; constructor => //.
  Qed.
  Definition u := t.
  Definition u_of_t (x : t) : u := x.
  Definition t_of_u (y : u) : t := y.
  Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
  Proof. by []. Qed.
End DIntvNetPayload.
  
Module Forest (OUT : BOUND).

(* symbolically execute a forest *)
  
Module SYM_NetVec := Vector OUT DIntvNetPayload.
Module SYM_OutVec := Vector OUT DIntvPayload.

Definition SYM_ix_to_ix (x : SYM_OutVec.Ix.t) : SYM_NetVec.Ix.t :=
  match x with
  | SYM_OutVec.Ix.mk _ pf => SYM_NetVec.Ix.mk pf
  end.
Coercion SYM_ix_to_ix : SYM_OutVec.Ix.t >-> SYM_NetVec.Ix.t.

Definition seval (v : SYM_NetVec.t) : SYM_OutVec.t :=
  SYM_OutVec.of_fun (fun ix => seval (SYM_NetVec.get ix v)).

(* concretely execute a forest *)
  
Module CONC_NetVec := Vector OUT DNetPayload.
Module CONC_OutVec := Vector OUT DPayload.

Definition CONC_ix_to_ix (x : CONC_OutVec.Ix.t) : CONC_NetVec.Ix.t :=
  match x with
  | CONC_OutVec.Ix.mk _ pf => CONC_NetVec.Ix.mk pf
  end.
Coercion CONC_ix_to_ix : CONC_OutVec.Ix.t >-> CONC_NetVec.Ix.t.

Definition eval (v : CONC_NetVec.t) : CONC_OutVec.t :=
  CONC_OutVec.of_fun (fun ix => DRed.build (eval (CONC_NetVec.get ix v))).

End Forest.