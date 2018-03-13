Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith Reals Rpower Ranalysis Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import numerics.

Delimit Scope R_scope with R.

Fixpoint big_sum (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c + big_sum cs' f)%R
  else 0%R.

Lemma big_sum_nmul (T : Type) (cs : seq T) (f : T -> R) :
  (big_sum cs (fun c => - f c) = - big_sum cs [eta f])%R.
Proof.
  elim: cs=> /=; first by rewrite Ropp_0.
    by move=> a l IH; rewrite Ropp_plus_distr IH.
Qed.      

Lemma big_sum_ext' T U (cs : seq T) (cs' : seq U) f f' :
  length cs = length cs' ->
  (List.Forall
     (fun p =>
        let: (c, c') := p in
        f c = f' c')
     (zip cs cs')) -> 
  big_sum cs f = big_sum cs' f'.
Proof.
  move=> H H2; elim: cs cs' H H2; first by case.
  move => a l IH; case => // a' l' H H2; case: H => /= H3.
  by inversion H2; subst; rewrite H1 (IH l').
Qed.

Lemma big_sum_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sum cs f = big_sum cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sum_scalar T (cs : seq T) r f :
  (big_sum cs (fun c => r * f c) = r * big_sum cs (fun c => f c))%R.
Proof.
  elim: cs=> /=; first by rewrite Rmult_0_r.
    by move=> a l IH; rewrite IH /=; rewrite Rmult_plus_distr_l.
Qed.      

Lemma big_sum_plus T (cs : seq T) f g :
  (big_sum cs (fun c => f c + g c) =
   big_sum cs (fun c => f c) + big_sum cs (fun c => g c))%R.
Proof.
  elim: cs=> /=; first by rewrite Rplus_0_r.
  move=> a l IH; rewrite IH /=.
  rewrite [((_ + big_sum l (fun c => f c) + _))%R]Rplus_assoc.
  rewrite [(big_sum l (fun c => f c) + (_ + _))%R]Rplus_comm.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.  
  f_equal.
  f_equal.
  by rewrite Rplus_comm.
Qed.      

Lemma rat_to_R_sum T (cs : seq T) (f : T -> rat) :
  rat_to_R (\sum_(c <- cs) (f c)) =  
  big_sum cs (fun c => (rat_to_R (f c)))%R.
Proof.
  elim: cs=> //=; first by rewrite big_nil rat_to_R0.
  move=> a' l IH; rewrite big_cons.
  rewrite rat_to_R_plus IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
Qed.    

Lemma big_sum_constant T (cs : seq T) n :
  (big_sum cs (fun _ => n) = INR (size cs) * n)%R.
Proof.
  elim: cs => //=.
  { by rewrite Rmult_0_l. }
  move => t0 l ->.
  case: (size l).
  { by rewrite /INR Rmult_0_l Rmult_1_l Rplus_0_r. }
  move => x.
  field.
Qed.
  
Fixpoint big_product (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c * big_product cs' f)%R
  else 1%R.

Lemma big_product_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_product cs f = big_product cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_product_ge0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (0 <= big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rle_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  rewrite H2; apply: Rmult_le_compat.
  by apply: Rle_refl.
  by apply: Rle_refl.
  by apply: H; rewrite in_cons; apply/orP; left.
  apply: IH=> c H3; apply: H.
  by rewrite in_cons; apply/orP; right.
Qed.

Lemma big_product_gt0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 < f c)%R ->
  (0 < big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rlt_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  apply: Rmult_lt_0_compat.
  by apply: H; rewrite in_cons; apply/orP; left.
  by apply: IH=> c H3; apply: H; rewrite in_cons; apply/orP; right.
Qed.      
  
Lemma ln_big_product_sum (T : eqType) (cs : seq T) (f : T -> R) :
  (forall t : T, 0 < f t)%R -> 
  ln (big_product cs f) = big_sum cs (fun c => ln (f c)).
Proof.
  elim: cs=> /=; first by rewrite ln_1.
  move=> a l IH H; rewrite ln_mult=> //; first by rewrite IH.
    by apply: big_product_gt0.
Qed.    

Lemma big_product_exp_sum (T : eqType) (cs : seq T) (f : T -> R) :
  big_product cs (fun x => exp (f x)) = exp (big_sum cs f).
Proof.
  elim: cs => //=; first by rewrite exp_0.
  by move => a l IH; rewrite IH exp_plus.
Qed.  

Lemma big_product_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (forall c, c \in cs -> 0 <= g c)%R ->
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_product cs f <= big_product cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _ _ _; apply: Rle_refl. }
  move=> a l IH H1 H2 H3; apply Rmult_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
  { apply: big_product_ge0.
      by move=> c H4; apply: H1; rewrite in_cons; apply/orP; right. }
  { by apply: H3; rewrite in_cons; apply/orP; left. }
  apply: IH.
  { by move=> c H; apply: H1; rewrite in_cons; apply/orP; right. }
  { by move=> c H; apply: H2; rewrite in_cons; apply/orP; right. }
    by move=> c H; apply: H3; rewrite in_cons; apply/orP; right.
Qed.    

Lemma big_sum_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_sum cs f <= big_sum cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _; apply: Rle_refl. }
  move=> a l IH H1; apply Rplus_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
    by apply: IH=> c H; apply: H1; rewrite in_cons; apply/orP; right.
Qed.    

Lemma rat_to_R_prod T (cs : seq T) (f : T -> rat) :
  rat_to_R (\prod_(c <- cs) (f c)) =  
  big_product cs (fun c => (rat_to_R (f c)))%R.
Proof.
  elim: cs=> //=; first by rewrite big_nil rat_to_R1.
  move=> a' l IH; rewrite big_cons.
  rewrite rat_to_R_mul IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
Qed.    

(*TODO: All these bigops should really be consolidated at some point...sigh*)

(** Q bigops *)

Delimit Scope Q_scope with Q.

Fixpoint big_sumQ (T : Type) (cs : seq T) (f : T -> Q) : Q :=
  if cs is [:: c & cs'] then (f c + big_sumQ cs' f)%Q
  else 0%Q.

Lemma big_sumQ_nmul (T : Type) (cs : seq T) (f : T -> Q) :
  Qeq (big_sumQ cs (fun c => - f c))%Q (- big_sumQ cs [eta f])%Q.
Proof.
  elim: cs=> /=; first by [].
    by move => a l IH; rewrite IH Qopp_plus.
Qed.

Lemma big_sumQ_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sumQ cs f = big_sumQ cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sumQ_scalar T (cs : seq T) r f :
  Qeq (big_sumQ cs (fun c => r * f c))%Q (r * big_sumQ cs (fun c => f c))%Q.
Proof.
  elim: cs=> /=. rewrite Qmult_0_r. apply Qeq_refl.
    by move => a l IH; rewrite IH Qmult_plus_distr_r.
Qed.

(** N bigops *)

Fixpoint big_sumN (T : Type) (cs : seq T) (f : T -> N) : N :=
  if cs is [:: c & cs'] then (f c + big_sumN cs' f)%num
  else 0%num.

Lemma big_sumN_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sumN cs f = big_sumN cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sumN_scalar T (cs : seq T) r f :
  eq (big_sumN cs (fun c => r * f c))%num (r * big_sumN cs (fun c => f c))%num.
Proof.
  elim: cs=> /=. rewrite N.mul_0_r. apply N.eq_refl.
  by move => a l IH; rewrite IH Nmult_plus_distr_l.
Qed.
