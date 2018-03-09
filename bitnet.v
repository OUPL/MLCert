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

(* IEEE 754 convention: 
   - high-order bit is sign bit 
   - next EXPONENT_BITS.n bits are exponent bits 
   - remaining bits are significand bits *)
Module DyadicFloat (N : BOUND) (EXPONENT_BITS : BOUND).
  Module BitVecPayload := BitVectorPayload N.
  Module BitVec := BitVecPayload.BVec. Import BitVec.
  
  Definition size : N := N.of_nat n.
  
  Lemma sign_pf : is_true (N.to_nat (N.pred size) < n).
  Proof.
    move: N.n_gt0; move/ltP => H; rewrite /size.
    by rewrite N2Nat.inj_pred Nat2N.id; apply/ltP; apply: lt_pred_n_n.
  Qed.
  
  Definition sign : Ix.t := @Ix.mk (N.pred size) sign_pf.  
  Definition exponent_start : N := size - 1 - N.of_nat EXPONENT_BITS.n.
  
  Local Open Scope D_scope.
  
  Definition dyadic_of_significand_bit (ix : Ix.t) (b_ix : Bit) : D :=
    if b_ix then Dmake 1 (match ix with Ix.mk n _ => 
                                        match (exponent_start-n)%N with
                                        | N0 => 1%positive (*bogus--can't occur*)
                                        | Npos p => p
                                        end
                          end)
    else D0.
                      
  Definition Z_of_exponent_bit (ix : Ix.t) (b_ix : Bit) : Z :=
    if b_ix then match ix with Ix.mk n _ =>
                               match (n-exponent_start)%N with
                               | N0 => 1%Z
                               | Npos p => Zpower.two_power_pos p
                               end
                 end
    else Z0.
  
  Definition exponent_Z (b : t) : Z := 
    foldr (fun ix b_ix (acc : Z) =>
             if N.ltb (exponent_start-1) (Ix.val ix) && N.ltb (Ix.val ix) (size-1)
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

  Definition bits_to_bvec (l : list N.t) : t :=
    BitVec.of_fun
      (fun ix => if ListDec.In_dec N.eq_dec (Ix.val ix) l then BI
                 else BO).

  (* examples for N=32*)
  Definition bvec32_0p15625 : t := bits_to_bvec [21%N;25%N;26%N;27%N;28%N;29%N].
  Definition bvec32_1p0 : t := bits_to_bvec [23%N;24%N;25%N;26%N;27%N;28%N;29%N].
  Definition bvec32_0p0 : t := BitVec.of_fun (fun ix => BO).
  Definition test_e := exponent bvec32_0p15625.
  Definition test_s := significand bvec32_0p15625.
  Definition test := to_dyadic bvec32_0p15625.
End DyadicFloat.


(*** 32-Bit FP Networks ***)
Module B32 <: BOUND. Definition n := 32. Lemma n_gt0 : 0 < n. Proof. by []. Qed. End B32.  
Module B32_EXPONENT_BITS <: BOUND.
  Definition n := 8.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B32_EXPONENT_BITS.  

Module DyadicFloat32 := DyadicFloat B32 B32_EXPONENT_BITS. Import DyadicFloat32.
Module BitVec32Payload := DyadicFloat32.BitVecPayload.
(*(*TEST:*) Extraction "test.ml" test_e test_s test.*)
(* construct two forests: 
     1) over 32-bit float
     2) over D 
   along with a map from 1) to 2). *)
Module DyadicFloat32Net (D OUT : BOUND).
  (* D = dimensionality 
     OUT = number of outputs *)
  Module F := ForestMap D OUT BitVec32Payload DPayload. Import F.
  Definition seval (rho : FT.NETEval.Env.t) (f : FT.t) : FU.Output.t :=
    F.FT_eval to_dyadic rho f.
End DyadicFloat32Net.  


(*** 16-Bit FP Networks ***)
Module B16 <: BOUND. Definition n := 16. Lemma n_gt0 : 0 < n. Proof. by []. Qed. End B16.  
Module B16_EXPONENT_BITS <: BOUND.
  Definition n := 5.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B16_EXPONENT_BITS.  
Module DyadicFloat16 := DyadicFloat B16 B16_EXPONENT_BITS. Import DyadicFloat16.
Module BitVec16Payload := DyadicFloat16.BitVecPayload.
(*(*TEST:*) Extraction "test.ml" test_e test_s test.*)
Module DyadicFloat16Net (D OUT : BOUND).
  (* D = dimensionality 
     OUT = number of outputs *)
  Module F := ForestMap D OUT BitVec16Payload DPayload. Import F.
  Definition seval (rho : FT.NETEval.Env.t) (f : FT.t) : FU.Output.t :=
    F.FT_eval to_dyadic rho f.
End DyadicFloat16Net.  
