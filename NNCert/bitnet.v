Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith ZArith ProofIrrelevance. Import ListNotations.

Require Import OUVerT.dyadic OUVerT.numerics OUVerT.vector OUVerT.compile.
Require Import net.

Local Open Scope nat_scope.

Inductive Bit : Type := BI | BO.

Module BitPayload <: PAYLOAD.
  Definition t := Bit.
  Definition t0 := BO.
  Definition eq0 (x : t) :=
    match x with
    | BO => true
    | BI => false
    end.
  Lemma eq0P (x : t) : reflect (x = t0) (eq0 x).
  Proof. by rewrite /t0; case: x; constructor. Qed.
  Definition u := t.
  Definition u_of_t (x : t) : u := x.
  Definition t_of_u (y : u) : t := y.
  Lemma t_of_u_t (x : t) : t_of_u (u_of_t x) = x.
  Proof. by []. Qed.
End BitPayload.

Module BitVectorPayload (B : BOUND) <: PAYLOAD.
  Module BVec := Vector B BitPayload. Include BVec.
  Definition t0 : t := BVec.M.empty _.
  Definition eq0 (v : t) := BVec.M.is_empty v.
  Lemma eq0P v : reflect (v=t0) (eq0 v).
  Proof.
    rewrite /eq0 /BVec.M.is_empty /BVec.M.Raw.is_empty /t0.
    case: v => x y /=; move: y; case: x => y; constructor => //.     
    case H: BVec.M.empty => [z w]; inversion H; subst.
    f_equal; f_equal; apply: proof_irrelevance.
  Qed.
  (*I'd like to be able to let u equal something like: 
      {m : t & {f : BVec.ty & BVec.match_vecs m f}} 
    However, this really messes up extraction (even if the sigma type is 
    made noncomputation). The main issue is that, with the type above, 
    a bunch of random Ssreflect stuff gets extracted, leading to extracted 
    OCaml code that doesn't compile :-/.*)
  Definition u := t.
  Definition u_of_t (m : t) : u := m.
  Definition t_of_u (f : u) : t := f.
  Lemma t_of_u_t : forall t0 : t, t_of_u (u_of_t t0) = t0.
  Proof. by []. Qed.
End BitVectorPayload.

Definition bool_of_Bit (b : Bit) : bool :=
  match b with
  | BI => true
  | BO => false
  end.

Coercion bool_of_Bit : Bit >-> bool.

(** For bit vector functions. *)
Module BitVectorPayloadC (B : BOUND).
  Module BVecPayload := BitVectorPayload B. Include BVecPayload.
  Definition bits_to_bvec (l : list N.t) : t :=
    BVec.of_fun
      (fun ix => if ListDec.In_dec N.eq_dec (Ix.val ix) l then BI
                 else BO).
End BitVectorPayloadC.


(* IEEE 754 convention: 
   - high-order bit is sign bit 
   - next EXPONENT_BITS.n bits are exponent bits 
   - remaining bits are significand bits 
   - OFFSET.n is the exponent bias (15 for 16-bit, 127 for 32-bit) *)
Module DyadicFloat (N : BOUND) (EXPONENT_BITS : BOUND) (OFFSET : BOUND).
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
    if b_ix then DD (Dmake 1 (match ix with Ix.mk n _ => 
                                            match (exponent_start-n)%N with
                                            | N0 => 1%positive (*bogus--can't occur*)
                                            | Npos p => p
                                            end
                              end))
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
    | Zpos p => DD (Dmake (2 * (Zpower.two_power_pos p)) 1%positive)
    | Zneg n => DD (Dmake 1%Z n)
    end.

  Definition exponent (b : t) : D := two_pow (exponent_Z b - Z.of_nat OFFSET.n).

  Definition significand (b : t) :=
    foldr (fun ix b_ix acc =>
             if N.ltb (Ix.val ix) exponent_start
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

(*I would like to use DPayload as defined in OUVerT/vector.v. However, that 
  instantiation causes extraction issues. FIXME: RESOLVED?*)
Module DPayload <: PAYLOAD.
  Definition t := DRed.t.   
  Definition t0 := 0%DRed.
  Definition eq0 (dx : t) :=
    if Deq_dec dx.(DRed.d) 0 then true else false.
  Lemma eq0P (dx : t) : reflect (dx=0%DRed) (eq0 dx).
  Proof.
    rewrite /eq0; case: (Deq_dec dx.(DRed.d) 0) => a; constructor.
    { case: dx a => /= d pf H; subst d; unfold DRed.t0.
      f_equal; apply: proof_irrelevance. }
    by inversion 1; case: dx H H0 a => d pf; case => H /= _; subst d.
  Qed.
  Definition u := t.
  Definition u_of_t (dx : t) : u := dx.
  Definition t_of_u (r : u) : t := r.
  Lemma t_of_u_t : forall t0 : t, t_of_u (u_of_t t0) = t0. Proof. by []. Qed.
End DPayload.  

(*** 32-Bit FP Networks ***)
Module B32 <: BOUND. Definition n := 32. Lemma n_gt0 : 0 < n. Proof. by []. Qed. End B32.  
Module B32_EXPONENT_BITS <: BOUND.
  Definition n := 8.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B32_EXPONENT_BITS.
Module B32_OFFSET <: BOUND.
  Definition n := 127.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B32_OFFSET.

Module DyadicFloat32 := DyadicFloat B32 B32_EXPONENT_BITS B32_OFFSET. Import DyadicFloat32.
Module BitVec32Payload := DyadicFloat32.BitVecPayload.
(*(*TEST:*) Extraction "test.ml" test_e test_s test.*)
(* construct two forests: 
     1) over 32-bit float
     2) over D 
   along with a map from 1) to 2). *)
Module DyadicFloat32Net (IN D OUT : BOUND).
  (* IN = input dimensionality 
     D = number of parameters
     OUT = number of outputs *)
  Module F := ForestMap IN D OUT BitVec32Payload DPayload. Import F.
  Definition seval
             (theta : FT.NETEval.ParamEnv.t)
             (f : FT.t)
             (rho : FT.NETEval.InputEnv.t) : FU.Output.t :=
    F.FT_eval to_dyadic theta f rho.
End DyadicFloat32Net.  


(*** 16-Bit FP Networks ***)
Module B16 <: BOUND. Definition n := 16. Lemma n_gt0 : 0 < n. Proof. by []. Qed. End B16.
Module B16_EXPONENT_BITS <: BOUND.
  Definition n := 5.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B16_EXPONENT_BITS.
Module B16_OFFSET <: BOUND.
  Definition n := 15.
  Lemma n_gt0 : 0 < n. Proof. by []. Qed.
End B16_OFFSET.
Module DyadicFloat16 := DyadicFloat B16 B16_EXPONENT_BITS B16_OFFSET. Import DyadicFloat16.
Module BitVec16Payload := DyadicFloat16.BitVecPayload.
(*(*TEST:*) Extraction "test.ml" test_e test_s test.*)
Module DyadicFloat16Net (IN D OUT : BOUND).
  (* IN = input dimensionality 
     D = number of parameters
     OUT = number of outputs *)
  Module F := ForestMap IN D OUT BitVec16Payload DPayload. Import F.
  Definition seval
             (theta : FT.NETEval.ParamEnv.t)
             (f : FT.t)
             (rho : FT.NETEval.InputEnv.t) : FU.Output.t :=
    F.FT_eval to_dyadic theta f rho.
End DyadicFloat16Net.


(*** Dyadic Networks ***)
Module DyadicNet (IN D OUT : BOUND).
  (* IN = input dimensionality 
     D = number of parameters
     OUT = number of outputs *)
  Module F := Forest IN D OUT DPayload. Import F.
  Definition seval
             (theta : F.NETEval.ParamEnv.t)
             (f : F.t)
             (rho : F.NETEval.InputEnv.t) : F.Output.t :=
    F.seval theta f rho.
End DyadicNet.
