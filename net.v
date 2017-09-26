Set Implicit Arguments.

Require Import List NArith. Import ListNotations.

Require Import dyadic numerics.

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

(*
Fixpoint feval_comb (acc : (D * D)) (l : list (weight * (D * D))) : (D * D) :=
  match l with
  | (w, (lo, hi)) :: l' =>    
    let acc' :=
        if Dlt_bool w 0 then (Dred (fst acc + w * hi), Dred (snd acc + w * lo))
        else (Dred (fst acc + w * lo), Dred (snd acc + w * hi))
    in feval_comb acc' l'
  | [] => acc
  end.
*)

Fixpoint feval_comb {T} `{domain T} (acc : T) (l : list (weight * T)) : T :=
  match l with
  | (w, t) :: l' => feval_comb (dadd (dmult w t) acc) l'
  | [] => acc
  end.

(*
Fixpoint feval (n : net) : (D * D) :=
  match n with
  | NIn lo hi => (Dred lo, Dred hi)
  | NReLU n' => (0, snd (feval n'))
  | NComb l =>
    let l' := map (fun p => (fst p, feval (snd p))) l
    in feval_comb (0, 0) l'
  end.
 *)

Fixpoint feval {T} `{domain T} (n : net) : T :=
  match n with
  | NIn t => dred t
  | NReLU n' => dred (drelu (feval n'))
  | NComb l =>
    let l' := map (fun p => (fst p, feval (snd p))) l
    in dred (feval_comb (dmeet dzero_inf dinf_zero) l')
  end.

Definition v11 := NIn (Dlh 0 1).
Compute feval v11.
Definition v21b := NComb [(1,v11)].
Compute feval v21b.
Definition v22b := NComb [(-(1),v11)].
Compute feval v22b.
Definition v21f := NReLU v21b.
Compute feval v21f.
Definition v22f := NReLU v22b.
Compute feval v22f.
Definition v31 := NComb [(1,v21f); (1,v22f)].
Compute feval v31.

