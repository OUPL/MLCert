Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith ZArith. Import ListNotations.

Require Import dyadic numerics vector compile net.

Definition bool_of_Bit (b : Bit) : bool :=
  match b with
  | BI => true
  | BO => false
  end.

Coercion bool_of_Bit : Bit >-> bool.

Module B32 <: BOUND.
  Definition n := 32.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B32.  

Module BitVec32 := Vector B32 BitPayload. Import BitVec32.

Section bitvec32_to_dyadic.
  Lemma sign_pf : is_true (N.to_nat 31 < n). Proof. by []. Qed.
  
  Definition sign : Ix.t := @Ix.mk 31%N sign_pf.

  Local Open Scope D_scope.

  Definition dyadic_of_significand_bit (ix : Ix.t) (b_ix : Bit) : D :=
    if b_ix then Dmake 1 (match ix with Ix.mk n _ => 
                                        match (23-n)%N with
                                        | N0 => 1%positive (*bogus--can't occur*)
                                        | Npos p => p
                                        end
                          end)
    else D0.
                      

  Definition Z_of_exponent_bit (ix : Ix.t) (b_ix : Bit) : Z :=
    if b_ix then match ix with Ix.mk n _ =>
                               match (n-23)%N with
                               | N0 => 1%Z
                               | Npos p => Zpower.two_power_pos p
                               end
                 end
    else Z0.
  
  Definition exponent_Z (b : t) : Z := 
    foldr (fun ix b_ix (acc : Z) =>
             if N.ltb 22 (Ix.val ix) && N.ltb (Ix.val ix) 31
             then (acc + Z_of_exponent_bit ix b_ix)%Z
             else acc) b 0%Z.

  (* two_pow z = 2^z : D *)
  Definition two_pow (z : Z) : D :=
    match z with
    | Z0 => D1
    | Zpos p => Dmake (2 * (Zpower.two_power_pos p)) 1%positive
    | Zneg n => Dmake 1%Z n
    end.

  Definition exponent (b : t) : D := two_pow (exponent_Z b - 127).
  
  Definition significand (b : t) :=
    foldr (fun ix b_ix acc =>
             if N.ltb (Ix.val ix) 23
             then acc + dyadic_of_significand_bit ix b_ix
             else acc) b 1. (*significand = 1 + interp(bits)*)
      
  Definition to_dyadic (b : t) :=
    Dred ((if BitPayload.eq0 (get sign b) then 1 else -(1)) * (*sign bit*)
          significand b *
          exponent b).

  (* examples *)
  Definition bvec_0p15625 : t :=
    BitVec32.of_fun
      (fun ix => if N.eqb (Ix.val ix) 21 then BI
                 else if N.eqb (Ix.val ix) 25 then BI
                 else if N.eqb (Ix.val ix) 26 then BI
                 else if N.eqb (Ix.val ix) 27 then BI                                                          
                 else if N.eqb (Ix.val ix) 28 then BI
                 else if N.eqb (Ix.val ix) 29 then BI                                                          
                      else BO).
  Definition bvec_1p0 : t :=
    BitVec32.of_fun
      (fun ix => if N.eqb (Ix.val ix) 23 then BI                                                
                 else if N.eqb (Ix.val ix) 24 then BI                                                
                 else if N.eqb (Ix.val ix) 25 then BI
                 else if N.eqb (Ix.val ix) 26 then BI
                 else if N.eqb (Ix.val ix) 27 then BI                                                          
                 else if N.eqb (Ix.val ix) 28 then BI
                 else if N.eqb (Ix.val ix) 29 then BI                                                          
                      else BO).
  Definition bvec_0p0 : t :=
    BitVec32.of_fun (fun ix => BO).
  Definition test_e := exponent bvec_0p15625.
  Definition test_s := significand bvec_0p15625.
  Definition test := to_dyadic bvec_0p15625.
End bitvec32_to_dyadic.
(*(*TEST:*) Extraction "test.ml" test_e test_s test.*)

(* A vacuous domain for size-32 bitvectors (NOTE: to interpret 
   bitnets, we first map to D using to_dyadic above, then interpret 
   in domain_D as defined in net.v). *)
Instance vacuous_domain_bitvec32 : domain BitVec32.t :=
  mkDomain
    bvec_0p0 bvec_0p0 (fun x _ => x) (fun x _ => x)
    (fun x => x) (fun x _ => x) (fun _ x => x) (fun x => x).

Definition dyadic_of_float32_net (n : 



(* A forest of size-32 bitvector nets: 
   -OUT: The number of output nodes *)
Module Float32Net (OUT : BOUND).

  (* Nets over size-32 bitvectors *)
  Module Float32NetPayload <: PAYLOAD.
    Definition t := @net BitVec32.t _.
  Definition t0 := NIn bvec_0p0.
  Definition eq0 (x : t) :=
    match x with
    | NIn f =>
      match BitVec32.any (fun _ b => b) f with
      | None => true
      | Some _ => false
      end
    | _ => false
    end.
  Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
  Proof. Admitted.
  Definition u := t.
  Definition u_of_t (x : t) : u := x.
  Definition t_of_u (y : u) : t := y.
  Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
  Proof. by []. Qed.
End Float32NetPayload.


  
  Module BitNet := Vector OUT B
Module BIT_NetVec := Vector OUT (BitVectorPayload B).
Module SYM_OutVec := Vector OUT DIntvPayload.

Definition SYM_ix_to_ix (x : SYM_OutVec.Ix.t) : SYM_NetVec.Ix.t :=
  match x with
  | SYM_OutVec.Ix.mk _ pf => SYM_NetVec.Ix.mk pf
  end.
Coercion SYM_ix_to_ix : SYM_OutVec.Ix.t >-> SYM_NetVec.Ix.t.

Definition seval (v : SYM_NetVec.t) : SYM_OutVec.t :=
  SYM_OutVec.of_fun (fun ix => seval (SYM_NetVec.get ix v)).


