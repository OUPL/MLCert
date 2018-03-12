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

Module Net (IN D : BOUND) (T : PAYLOAD).
  (* IN = dimensionality of the input space
     D = the number of parameters
     T = the type of network inputs/weights*)

  Module InputEnv := Vector IN T.
  Module ParamEnv := Vector D T.
  Definition input_var := InputEnv.Ix.t.
  Definition param_var := ParamEnv.Ix.t.  
  
  Inductive t : Type :=
  | NIn : input_var -> t
  | NReLU : t -> t
  | NComb : list (param_var * t) -> t.
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

Definition Dmult (c : Dintv) (d : Dintv) : Dintv :=
  match c with
  | Dpos c' => let d' := Dmult_aux c' d in if Dlt_bool c' 0 then Dinv d' else d'
  | Dneg c' => let d' := Dmult_aux c' d in if Dlt_bool c' 0 then Dinv d' else d'
  | _ => Dbot
  end.

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
      dmult : T -> T -> T;
      dred : T -> T;
    }.

Instance domain_Dpair : domain Dintv :=
  mkDomain (Dpos 0) (Dneg 0) Dmeet Djoin Drelu Dadd Dmult Dreduce.

(* symbolic execution *)

Module NetEval (IN D : BOUND) (T : PAYLOAD).
  Module NET := Net IN D T. Include NET.

  Fixpoint seval_comb `{domain T.t}
           (theta : NET.ParamEnv.t)
           (acc : T.t)
           (l : list (param_var * T.t)) : T.t :=
    match l with
    | (x, t) :: l' => seval_comb theta (dadd (dmult (NET.ParamEnv.get x theta) t) acc) l'
    | [] => acc
    end.

  (* rho = input vector 
     theta = parameter vector *)
  Fixpoint seval `{domain T.t}
           (theta : NET.ParamEnv.t)
           (n : NET.t)
           (rho : NET.InputEnv.t)
    : T.t :=
    match n with
    | NIn x => dred (NET.InputEnv.get x rho)
    | NReLU n' => dred (drelu (seval theta n' rho))
    | NComb l =>
      let l' := map (fun p => (fst p, seval theta (snd p) rho)) l
      in dred (seval_comb theta (dmeet dzero_inf dinf_zero) l')
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
  Definition n:nat := 2.
  Lemma n_gt0 : (0 < n)%nat. by []. Qed.
End Test1Bound.
Module Test1 := NetEval Test1Bound Test1Bound DIntvPayload. Import Test1. Import NET.
Program Definition x : input_var := @InputEnv.Ix.mk 0 _.
Program Definition p0 : param_var := @ParamEnv.Ix.mk 0 _.
Program Definition p1 : param_var := @ParamEnv.Ix.mk 1 _.
Definition rho : InputEnv.t := InputEnv.of_fun (fun _ => Dlh 0 1).
Definition theta : ParamEnv.t :=
  ParamEnv.of_fun (fun i => match i with
                            | ParamEnv.Ix.mk i' _ => if N.eqb i' 0 then Dpos 1 else Dneg 1
                            end).
Definition v11 := NIn x.
Definition v21b := NComb [(p0,v11)].
Definition v22b := NComb [(p1,v11)].
Definition v21f := NReLU v21b.
Definition v22f := NReLU v22b.
Definition v31 := NComb [(p1,v21f); (p1,v22f)].
End Test1Symbolic.

Instance domain_D : domain D :=
  mkDomain
    0 0 (fun x _ => x) (fun x _ => x)
    (fun x => Dmax 0 x)
    dyadic.Dadd
    dyadic.Dmult
    Dred.

Instance domain_DRed : domain DRed.t :=
  mkDomain
    (DRed.build 0) (DRed.build 0) (fun x _ => x) (fun x _ => x)
    (fun x => DRed.build (Dmax 0 x))
    DRed.add
    DRed.mult
    (fun x => x).

Module Test1Concrete.
Module Test1Bound <: BOUND.
  Definition n:nat := 2.
  Lemma n_gt0 : (0 < n)%nat. by []. Qed.
End Test1Bound.
Module Test1 := NetEval Test1Bound Test1Bound DPayload. Import Test1. Import NET.
Program Definition x : input_var := @InputEnv.Ix.mk 0 _.
Program Definition p0 : param_var := @ParamEnv.Ix.mk 0 _.
Program Definition p1 : param_var := @ParamEnv.Ix.mk 1 _.
Definition rho : InputEnv.t := InputEnv.of_fun (fun _ => DRed.build (Dmake 8 1)).
Definition theta : ParamEnv.t :=
  ParamEnv.of_fun (fun i => match i with
                            | ParamEnv.Ix.mk i' _ =>
                              if N.eqb i' 0 then DRed.build 1
                              else DRed.build (-(1))
                            end).
Definition v11' := NIn x.
Definition v21b' := NComb [(p0,v11')].
Definition v22b' := NComb [(p1,v11')].
Definition v21f' := NReLU v21b'.
Definition v22f' := NReLU v22b'.
Definition v31' := NComb [(p0,v21f'); (p0,v22f')].
End Test1Concrete.

(* forests of nets *)

Module Forest (IN D OUT : BOUND) (T : PAYLOAD).
  (* I = dimensionality of input space 
     D = number of parameters
     OUT = number of outputs 
     T = payload *)
  Module NETEval := NetEval IN D T. Import NETEval.
  Module NETPayload <: PAYLOAD.
    Definition t := NETEval.t.
    Definition i0 : NET.input_var := @NET.InputEnv.Ix.mk 0%N IN.n_gt0.
    Definition t0 := NET.NIn i0.
    Definition eq0 (x : t) :=
      match x with
      | NIn y => match y with
                 | NET.InputEnv.Ix.mk z _ => 
                     if Nat.eq_dec (N.to_nat z) 0 then true else false
                 end
      | _ => false
      end.
    Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
    Proof.
      rewrite /t0; case: x => /=.
      { case => /= x pf; rewrite /i0.
        destruct (Nat.eq_dec (N.to_nat x) O) eqn:H.
        { subst; constructor; f_equal; apply/NET.InputEnv.Ix.eqP.
          rewrite /NET.InputEnv.Ix.eq /=; clear H pf.
          by case: x e => //= p e; move: (PosN0 p); rewrite e. }
        { constructor; inversion 1; subst.
          by simpl in n; elimtype False. }}
      { move => l; constructor => //. }
      move => l; constructor => //.
    Qed.
    Definition u := t.
    Definition u_of_t (x : t) : u := x.
    Definition t_of_u (y : u) : t := y.
    Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
    Proof. by []. Qed.
  End NETPayload.

  (* a forest is an OUT-vector of NETs *)
  Module Forest := Vector OUT NETPayload. Definition t := Forest.t.
  Module Output := Vector OUT T.

  (* execute a forest *)
  Definition Output_ix_to_ix (x : Output.Ix.t) : Forest.Ix.t :=
    match x with
    | Output.Ix.mk _ pf => Forest.Ix.mk pf
    end.
  Coercion Output_ix_to_ix : Output.Ix.t >-> Forest.Ix.t.

  Definition seval `{domain T.t} 
             (theta : ParamEnv.t)
             (f : Forest.t)
             (rho : InputEnv.t) : Output.t :=
    Output.of_fun (fun ix => Forest.NETEval.seval theta (Forest.get ix f) rho).
End Forest.

(* map a forest payload from T to U *)

Module ForestMap (IN D OUT : BOUND) (T U : PAYLOAD).
  Module FT := Forest IN D OUT T.
  Module FU := Forest IN D OUT U.

  Section forest_map.
    Variable F : T.t -> U.t.

    Definition FU_ix_to_ix (x : FU.Forest.Ix.t) : FT.Forest.Ix.t :=
      match x with
      | FU.Forest.Ix.mk _ pf => FT.Forest.Ix.mk pf
      end.
    Coercion FU_ix_to_ix : FU.Forest.Ix.t >-> FT.Forest.Ix.t.

    Definition FT_to_FU_input_var (x : FT.NETEval.NET.input_var) : FU.NETEval.NET.input_var :=
      match x with
      | FT.NETEval.NET.InputEnv.Ix.mk _ pf => FU.NETEval.NET.InputEnv.Ix.mk pf
      end. Coercion FT_to_FU_input_var : FT.NETEval.NET.input_var >-> FU.NETEval.NET.input_var.
    Definition FU_to_FT_input_var (x : FU.NETEval.NET.input_var) : FT.NETEval.NET.input_var := 
      match x with
      | FU.NETEval.NET.InputEnv.Ix.mk _ pf => FT.NETEval.NET.InputEnv.Ix.mk pf
      end. Coercion FU_to_FT_input_var : FU.NETEval.NET.input_var >-> FT.NETEval.NET.input_var.

    Definition FT_to_FU_param_var (x : FT.NETEval.NET.param_var) : FU.NETEval.NET.param_var :=
      match x with
      | FT.NETEval.NET.ParamEnv.Ix.mk _ pf => FU.NETEval.NET.ParamEnv.Ix.mk pf
      end. Coercion FT_to_FU_param_var : FT.NETEval.NET.param_var >-> FU.NETEval.NET.param_var.
    Definition FU_to_FT_param_var (x : FU.NETEval.NET.param_var) : FT.NETEval.NET.param_var := 
      match x with
      | FU.NETEval.NET.ParamEnv.Ix.mk _ pf => FT.NETEval.NET.ParamEnv.Ix.mk pf
      end. Coercion FU_to_FT_param_var : FU.NETEval.NET.param_var >-> FT.NETEval.NET.param_var.
    
    Fixpoint net_map (n : FT.NETPayload.t) : FU.NETPayload.t :=
      match n with
      | FT.NETEval.NIn x => FU.NETEval.NIn x
      | FT.NETEval.NReLU n' => FU.NETEval.NReLU (net_map n')
      | FT.NETEval.NComb l =>
        FU.NETEval.NComb (map (fun p => (FT_to_FU_param_var p.1, net_map p.2)) l)
      end.
    
    Definition forest_map (f : FT.t) : FU.t :=
      FU.Forest.of_fun (fun ix => net_map (FT.Forest.get ix f)).

    (* evaluate a T-forest by first mapping to a U-forest, then evaluating *)
    Definition FT_eval `{domain U.t}
               (theta : FT.NETEval.ParamEnv.t)                
               (f : FT.t)
               (rho : FT.NETEval.InputEnv.t) : FU.Output.t :=
      FU.seval
        (FU.NETEval.ParamEnv.of_fun
           (fun ix => F (FT.NETEval.ParamEnv.get (FU_to_FT_param_var ix) theta)))
        (forest_map f)
        (FU.NETEval.InputEnv.of_fun
           (fun ix => F (FT.NETEval.InputEnv.get (FU_to_FT_input_var ix) rho))).        
  End forest_map.
End ForestMap.


