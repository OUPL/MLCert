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

Module BitVec32Payload := BitVectorPayload B32.
Module BitVec32 := BitVec32Payload.BVec. Import BitVec32.

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
      
  Definition to_dyadic (b : t) : DRed.t :=
    DRed.build
      ((if BitPayload.eq0 (get sign b) then 1 else -(1)) * (*sign bit*)
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

(* construct two forests: 
     1) over BitVec32.t 
     2) over D 
   along with a map from 1) to 2). *)
Module DyadicFloatNet (D OUT : BOUND).
  (* D = dimensionality 
     OUT = number of outputs *)
  Module F := ForestMap D OUT BitVec32Payload DPayload. Import F.

  Definition seval (rho : FT.NETEval.Env.t) (f : FT.t) : FU.Output.t :=
    F.FT_eval to_dyadic rho f.
End DyadicFloatNet.  
  