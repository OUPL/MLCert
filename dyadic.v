Require Import ZArith PArith QArith ProofIrrelevance.

Record D : Set :=
  Dmake { num : Z;
          den : positive }.

Definition pow_pos (p r : positive) : positive :=
  Pos.iter (Pos.mul p) 1%positive r.

Lemma pow_pos_Zpow_pos p r : Zpos (pow_pos p r) = Z.pow_pos (Zpos p) r.
Proof.
  unfold pow_pos, Z.pow_pos.
  rewrite !Pos2Nat.inj_iter; generalize (Pos.to_nat r) as n; intro.
  revert p; induction n; auto.
  intros p; simpl; rewrite <-IHn; auto.
Qed.

Definition D_to_Q (d : D) :=
  Qmake (num d) (shift_pos (den d) 1).

Definition D0 : D := Dmake 0 1.
Definition D1 : D := Dmake 2 1.

Lemma D_to_Q0' : D_to_Q D0 = 0 # 2.
Proof. auto. Qed.

Lemma D_to_Q0 : D_to_Q D0 == 0.
Proof. rewrite D_to_Q0'; unfold Qeq; simpl; auto. Qed.

Lemma D_to_Q1' : D_to_Q D1 = 2 # 2.
Proof. auto. Qed.

Lemma D_to_Q1 : D_to_Q D1 == 1.
Proof. rewrite D_to_Q1'; unfold Qeq; simpl; auto. Qed.

Definition Dadd (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    if Pos.ltb y1 y2 then
      Dmake (Z.pow_pos 2 (y2 - y1) * x1 + x2) y2
    else if Pos.ltb y2 y1 then 
           Dmake (Z.pow_pos 2 (y1 - y2) * x2 + x1) y1
         else Dmake (x1 + x2) y1
  end.

Lemma Qdiv_mult (s q r : Q) :
  ~ s == 0 -> 
  (q / r) == (q * s) / (r * s).
Proof.
  intros H; unfold Qdiv.
  assert (q * s * /(r * s) == q * /r) as ->.
  { rewrite Qinv_mult_distr, (Qmult_comm (/r)), Qmult_assoc.
    rewrite <-(Qmult_assoc q), Qmult_inv_r, Qmult_1_r; auto.
    apply Qeq_refl. }
  apply Qeq_refl.
Qed.

Lemma Qdiv_1_r q : q / 1 == q.
Proof.
  unfold Qdiv, Qinv; simpl; rewrite Qmult_1_r.
  apply Qeq_refl.
Qed.

Lemma Zdiv_pos0 (x y : positive) : (Zpos (x~0) / Zpos (y~0) = Zpos x / Zpos y)%Z.
Proof.
  rewrite Pos2Z.inj_xO, (Pos2Z.inj_xO y).
  rewrite Zdiv_mult_cancel_l; auto.
  inversion 1.
Qed.  

Lemma Zpow_pos_2exp (x y : nat) :
  (y < x)%nat -> 
  Z.pow 2 (Z.of_nat (x - y)) = (Z.pow 2 (Z.of_nat x) / Z.pow 2 (Z.of_nat y))%Z.
Proof.
  intros H; rewrite <-!two_power_nat_equiv; unfold two_power_nat.
  revert y H; induction x; simpl.
  { destruct y; try solve[inversion 1]. }
  destruct y; simpl.
  { intros H; rewrite Zdiv_1_r; auto. }
  intros H.
  rewrite IHx.
  { rewrite Zdiv_pos0; auto. }
  apply lt_S_n; auto.
Qed.

Lemma Pos_iter_swap' T f g (r : T) (x : positive) :
  (forall t, f (g t) = t) -> 
  Pos.iter f (Pos.iter g r x) x = r.
Proof.
  rewrite 2!Pos2Nat.inj_iter.
  assert (H: exists y, Pos.to_nat x = Pos.to_nat y).
  { exists x; auto. }
  revert H; generalize (Pos.to_nat x) as n; intros n H.
  revert r; induction n; simpl; auto.
  intros r H2.
  destruct (Nat.eq_dec n 0).
  { subst n.
    simpl.
    rewrite H2; auto. }
  assert (H3: exists y, n = Pos.to_nat y).
  { exists (Pos.of_nat n).
    rewrite Nat2Pos.id; auto. }
  destruct H3 as [y H3].
  subst n.
  rewrite <-Pos2Nat.inj_iter.
  rewrite <-Pos.iter_swap.
  rewrite H2.
  rewrite Pos2Nat.inj_iter.
  apply IHn; auto.
  exists y; auto.
Qed.  

Lemma Pos_lt_Zpos_Zlt x y :  
  (x < y)%positive -> 
  (' x < ' y)%Z.
Proof.
  unfold Z.lt; simpl; rewrite <-Pos.ltb_lt.
  rewrite Pos.ltb_compare.
  destruct (Pos.compare x y); auto; try solve[inversion 1].
Qed.  

Lemma Zlt_le x y : (x < y -> x <= y)%Z.
Proof.
  unfold Z.le; intros H.
  generalize (Zlt_compare _ _ H).
  destruct (Z.compare x y); try solve[inversion 1|auto].
  intros _; inversion 1.
Qed.

Lemma Zpow_pos_div x y :
  (y < x)%positive -> 
  (Z.pow_pos 2 x # 1) * / (Z.pow_pos 2 y # 1) == Z.pow_pos 2 (x - y) # 1.
Proof.
  intros H; rewrite !Z.pow_pos_fold.
  assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
  { apply Pos2Z.inj_sub; auto. }
  rewrite Z.pow_sub_r; try omega.
  rewrite <-Z.pow_sub_r.
  { unfold Qmult, Qinv; simpl.
    assert (exists p, Z.pow_pos 2 y = Zpos p).
    { unfold Z.pow_pos.
      rewrite Pos2Nat.inj_iter.
      generalize (Pos.to_nat y); induction n.
      { simpl. exists 1%positive; auto. }
      simpl in IHn|-*.
      destruct IHn as [p H2]; rewrite H2; exists (p~0%positive); auto. }
    destruct H0 as [p H1]; rewrite H1; simpl.
    unfold Qeq; simpl; rewrite <-H1.
    rewrite Z.pos_sub_gt; auto.
    rewrite 2!Z.pow_pos_fold.
    assert (2 ^ ' (x - y) * 2 ^ ' y = 2 ^ ' x)%Z as ->.
    { assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
      { rewrite <-Z_pos_sub_gt.
        { rewrite <-Pos2Z.add_pos_neg.
          unfold Z.sub; auto. }
        rewrite Pos.gt_lt_iff; auto. }
      assert (Hbounds : (0 <= ' y <= ' x)%Z).
      { split.
        { apply Pos2Z.is_nonneg. }
        apply Zlt_le.
        apply Pos_lt_Zpos_Zlt; auto. }
      rewrite Z.pow_sub_r; auto; [|inversion 1].
      rewrite <-Z.shiftr_div_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_mul_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_1_l.
      rewrite Z.shiftr_shiftl_l; [|apply Pos2Z.is_nonneg].
      rewrite Z.shiftl_shiftl.
      { rewrite Z.sub_simpl_r; auto. }
      destruct Hbounds.
      apply Zle_minus_le_0; auto. }
    rewrite 2!Zmult_1_r; auto. }
  { inversion 1. }
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Zle, Z.compare; rewrite H; inversion 1. 
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Zle, Z.compare; rewrite H; inversion 1. 
Qed.

Lemma Qinv_neq (n : Q) : ~0 == n -> ~0 == / n.
Proof.
  unfold Qeq, Qinv; simpl.
  destruct (Qnum _); simpl; auto.
  { intros _ H.
    generalize (Pos2Z.is_pos (Qden n * 1)).
    rewrite <-H; inversion 1. }
  intros _ H.
  generalize (Zlt_neg_0 (Qden n * 1)).
  rewrite <-H; inversion 1.
Qed.  

Lemma Qdiv_neq_0 n m : ~n==0 -> ~m==0 -> ~(n / m == 0).
Proof.
  intros H H1 H2.
  unfold Qdiv in H2.
  apply Qmult_integral in H2; destruct H2; auto.
  assert (H2: ~0 == m).
  { intros H2; rewrite H2 in H1; apply H1; apply Qeq_refl. }
  apply (Qinv_neq _ H2); rewrite H0; apply Qeq_refl.
Qed.  

Lemma Qmake_neq_0 n m : (~n=0)%Z -> ~(n # m) == 0.
Proof.
  intros H; unfold Qeq; simpl; intros H2.
  rewrite Zmult_1_r in H2; subst n; apply H; auto.
Qed.

Lemma Zpow_pos_neq_0 n m : (n<>0 -> Z.pow_pos n m <> 0)%Z.
Proof.
  intros H0.
  unfold Z.pow_pos.
  apply Pos.iter_invariant.
  { intros x H H2.
    apply Zmult_integral in H2; destruct H2.
    { subst; apply H0; auto. }
    subst x; apply H; auto. }
  inversion 1.
Qed.

Lemma Zmult_pow_plus x y r :
  (r <> 0)%Z -> 
  x * inject_Z (Z.pow r ('y)) / inject_Z (Z.pow r ('y+'y)) ==
  x / inject_Z (Z.pow r ('y)).
Proof.
  intros H; unfold inject_Z.
  assert (Hy: (' y >= 0)%Z).
  { generalize (Pos2Z.is_nonneg y).
    unfold Z.le, Z.ge; intros H2 H3.
    destruct (Zle_compare 0 ('y)); auto. }
  rewrite Zpower_exp; auto.
  unfold Qdiv.
  rewrite <-Qmult_assoc.
  assert (r^('y) * r^('y) # 1 == (r^('y)#1) * (r^('y)#1)) as ->.
  { unfold Qmult; simpl; apply Qeq_refl. }
  rewrite Qinv_mult_distr.
  rewrite (Qmult_assoc (r^('y)#1)).
  rewrite Qmult_inv_r, Qmult_1_l.
  { apply Qeq_refl. }
  apply Qmake_neq_0; intros H2.
  apply (Zpow_pos_neq_0 _ _ H H2).
Qed.  

Lemma Dadd_ok d1 d2 :
  D_to_Q (Dadd d1 d2) == D_to_Q d1 + D_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold Qplus; simpl.
  rewrite !shift_pos_correct, Qmake_Qdiv, !Pos2Z.inj_mul, !shift_pos_correct.
  rewrite !Zmult_1_r, !inject_Z_plus, !inject_Z_mult.
  assert (inject_Z (Z.pow_pos 2 X) * inject_Z (Z.pow_pos 2 Z) =
          inject_Z (Z.pow_pos 2 (X + Z))) as ->.
  { rewrite <-inject_Z_mult.
    symmetry; rewrite !Zpower_pos_nat.
    rewrite Pos2Nat.inj_add, Zpower_nat_is_exp; auto. }
  destruct (Pos.ltb X Z) eqn:H.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 X))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 X)) ==
             inject_Z Y * inject_Z (Z.pow_pos 2 (Z - X)) + inject_Z W)) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-Qmult_assoc.
      assert ((Z.pow_pos 2 Z # 1) * / (Z.pow_pos 2 X # 1) ==
              Z.pow_pos 2 (Z - X) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_l.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 X)) ==
            inject_Z (Z.pow_pos 2 Z)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 X) ==
              inject_Z (Z.pow_pos 2 Z)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite (Qmult_comm (inject_Z (Z.pow_pos 2 X))).
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold D_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 Z = Z.pow_pos 2 Z * ' 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm; apply Qeq_refl; auto.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  destruct (Pos.ltb Z X) eqn:H'.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 Z))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 Z)) ==
             inject_Z Y + inject_Z W * inject_Z (Z.pow_pos 2 (X - Z)))) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-(Qmult_assoc (W # 1)).
      assert ((Z.pow_pos 2 X # 1) * / (Z.pow_pos 2 Z # 1) ==
              Z.pow_pos 2 (X - Z) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_r.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 Z)) ==
            inject_Z (Z.pow_pos 2 X)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 Z) ==
              inject_Z (Z.pow_pos 2 X)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold D_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 X = Z.pow_pos 2 X * ' 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm, Z.add_comm; apply Qeq_refl.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  assert (H1: X = Z).
  { generalize H'; rewrite Pos.ltb_antisym.
    generalize H; unfold Pos.ltb, Pos.leb.
    destruct (X ?= Z)%positive eqn:H2; try solve[inversion 1|inversion 2].
    intros _ _.
    apply Pos.compare_eq; auto. }
  (* eq case *)
  subst Z; unfold D_to_Q; simpl; clear H H'.
  unfold Qdiv; rewrite Qmult_plus_distr_l.
  assert (inject_Z Y * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z Y / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }
  assert (inject_Z W * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z W / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }  
  unfold Qdiv; rewrite <-Qmult_plus_distr_l, Qmake_Qdiv, inject_Z_plus.
  unfold Qdiv; rewrite shift_pos_correct, Zmult_1_r; apply Qeq_refl.
Qed.

Definition Dmult (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    Dmake (x1 * x2) (y1 + y2)
  end.

Lemma shift_nat1_mult n m :
  (shift_nat n 1 * shift_nat m 1 = shift_nat n (shift_nat m 1))%positive.
Proof.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.
 
Lemma Dmult_ok d1 d2 :
  D_to_Q (Dmult d1 d2) = D_to_Q d1 * D_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold D_to_Q; simpl.
  unfold Qmult; simpl.
  rewrite !shift_pos_nat, Pos2Nat.inj_add, shift_nat_plus.
  rewrite shift_nat1_mult; auto.
Qed.

Definition Dopp (d : D) : D :=
  match d with
  | Dmake x y => Dmake (-x) y
  end.

Lemma Dopp_ok d : D_to_Q (Dopp d) = Qopp (D_to_Q d).
Proof.
  destruct d; simpl.
  unfold D_to_Q; simpl.
  unfold Qopp; simpl; auto.
Qed.

Definition Dsub (d1 d2 : D) : D := Dadd d1 (Dopp d2).

Lemma Dsub_ok d1 d2 :
  D_to_Q (Dsub d1 d2) == D_to_Q d1 - D_to_Q d2.
Proof.
  unfold Dsub.
  rewrite Dadd_ok.
  rewrite Dopp_ok.
  unfold Qminus; apply Qeq_refl.
Qed.

Definition Dle (d1 d2 : D) : Prop :=
  Qle (D_to_Q d1) (D_to_Q d2).  

(*TODO: There's probably a more efficient way to implement the following:*)
Definition Dle_bool (d1 d2 : D) : bool :=
  Qle_bool (D_to_Q d1) (D_to_Q d2).

Lemma Dle_bool_iff d1 d2 : (Dle_bool d1 d2 = true) <-> Dle d1 d2.
Proof.
  unfold Dle_bool, Dle.
  apply Qle_bool_iff.
Qed.

Definition Dlt (d1 d2 : D) : Prop :=
  Qlt (D_to_Q d1) (D_to_Q d2).  

Definition Dlt_bool (d1 d2 : D) : bool :=
  match D_to_Q d1 ?= D_to_Q d2 with
  | Lt => true
  | _ => false
  end.

Lemma Dlt_bool_iff d1 d2 : (Dlt_bool d1 d2 = true) <-> Dlt d1 d2.
Proof.
  unfold Dlt_bool; split.
  destruct (Qcompare_spec (D_to_Q d1) (D_to_Q d2));
    try solve[inversion 1|auto].
  unfold Dlt; rewrite Qlt_alt; intros ->; auto.
Qed.  

Lemma Deq_dec (d1 d2 : D) : {d1=d2} + {d1<>d2}.
Proof.
  destruct d1, d2.
  destruct (Z_eq_dec num0 num1).
  { destruct (positive_eq_dec den0 den1).
    left; subst; f_equal.
    right; inversion 1; subst; apply n; auto. }
  right; inversion 1; subst; auto.
Qed.  

(*(* MICROBENCHMARK *)
Fixpoint f (n : nat) (d : D) : D :=
  match n with
  | O => d
  | S n' => Dadd d (f n' d)
  end.

Time Compute f 5000 (Dmake 3 2).
(*Finished transaction in 0.012 secs (0.012u,0.s) (successful)*)

Fixpoint g (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => Qplus q (g n' q)
  end.

Time Compute g 5000 (Qmake 3 2).
(*Finished transaction in 0.847 secs (0.848u,0.s) (successful)*)
(*Speedup on this microbenchmark: 70x*)*)

Delimit Scope D_scope with D.
Bind Scope D_scope with D.
Arguments Dmake _%Z _%positive.

Infix "<" := Dlt : D_scope.
Infix "<=" := Dle : D_scope.
Notation "x > y" := (Dlt y x)(only parsing) : D_scope.
Notation "x >= y" := (Dle y x)(only parsing) : D_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : D_scope.

Infix "+" := Dadd : D_scope.
Notation "- x" := (Dopp x) : D_scope.
Infix "-" := Dsub : D_scope.
Infix "*" := Dmult : D_scope.

Notation "'0'" := D0 : D_scope.
Notation "'1'" := D1 : D_scope.

(** Dmax *)

Definition Dmax (d1 d2 : D) : D :=
  if Dlt_bool d1 d2 then d2 else d1.

(** The smallest power of 2 greater than a given rational *)

Definition Zsize (z : Z) : positive :=
  match z with
  | Z0 => 1
  | Zpos p => Pos.size p
  | Zneg p => Pos.size p
  end.

Definition Plub_aux (x : Z) (y : positive) : positive :=
  Zsize x - y.

Definition Dlub (max : D) : D :=
  match max with
  | Dmake x y => Dmake 1 (Plub_aux x y)
  end.

Lemma Zpos_2_mult (x : Z) (y : positive) :
  (x <= 'y)%Z -> (x * 2 <= 'y~0)%Z.
Proof.
  intros H.
  rewrite Zmult_comm.
  rewrite (Pos2Z.inj_xO y).
  apply Zmult_le_compat_l; auto.
  omega.
Qed.

Lemma two_power_pos_le x y :
  (x <= y)%positive -> (two_power_pos x <= two_power_pos y)%Z.
Proof.
  intros H.
  rewrite !two_power_pos_nat.
  rewrite Pos2Nat.inj_le in H.
  unfold two_power_nat, shift_nat.
  revert H.
  generalize (Pos.to_nat x) as x'; intro.
  generalize (Pos.to_nat y) as y'; intro.
  revert y'.
  induction x'; simpl.
  { intros y' _; induction y'; simpl; try solve[intros; omega].
    rewrite Pos2Z.inj_xO.
    assert ((1=1*1)%Z) as -> by (rewrite Zmult_1_r; auto).
    apply Zmult_le_compat; try omega. }
  induction y'; try solve[intros; omega].
  simpl; intros H.
  rewrite Pos2Z.inj_xO.
  rewrite
    (Pos2Z.inj_xO
       (nat_rect (fun _ : nat => positive) 1%positive 
                 (fun _ : nat => xO) y')).  
  apply Zmult_le_compat; try omega.
  { apply IHx'; omega. }
  clear - x'.
  induction x'; try (simpl; omega).
  simpl; rewrite Pos2Z.inj_xO.
  assert ((0=0*0)%Z) as -> by (rewrite Zmult_0_r; auto).
  apply Zmult_le_compat; try omega.
Qed.  

Lemma Zpow_pos_size_le x : (x <= Z.pow_pos 2 (Zsize x))%Z.
Proof.
  destruct x; simpl.
  { rewrite <-two_power_pos_correct.
    unfold two_power_pos; rewrite shift_pos_equiv; simpl; omega. }
  { generalize (Pos.lt_le_incl _ _ (Pos.size_gt p)).
    rewrite <-Pos2Z.inj_pow_pos; auto. }
  rewrite <-Pos2Z.inj_pow_pos.
  apply Zle_neg_pos.
Qed.  

Lemma Pos_succ_sub_1 p : (Pos.succ p - 1 = p)%positive.
Proof.
  set (P := fun p => (Pos.succ p - 1)%positive = p).
  change (P p); apply Pos.peano_ind; try reflexivity.
  intros r; unfold P; intros <-.
  rewrite <-Pos2Nat.inj_iff.
  rewrite nat_of_P_minus_morphism.
  { rewrite !Pos2Nat.inj_succ; auto. }
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  rewrite !Pos2Nat.inj_succ.
  rewrite Pos2Nat.inj_1.
  omega.
Qed.  

Lemma Pos_le_1_add_sub x : (x <= 1 + (x - 1))%positive.
Proof.
  set (P := fun x => (x <= 1 + (x - 1))%positive).
  change (P x).
  apply Pos.peano_ind.
  { unfold P; simpl. apply Pos.le_1_l. }
  intros p; unfold P; intros H.
  rewrite Pos_succ_sub_1.
  rewrite <-Pos.add_1_l.
  apply Pos.le_refl.
Qed.

Lemma Pos_succ_lt_2_false p : (Pos.succ p < 2)%positive -> False.
Proof.
  rewrite Pos2Nat.inj_lt.
  rewrite Pos2Nat.inj_succ.
  unfold Pos.to_nat; simpl.
  intros H.
  assert (H2: (2 < 2)%nat).
  { apply Nat.le_lt_trans with (m := S (Pos.iter_op Init.Nat.add p 1%nat)); auto.
    assert (H3: (1 <= Pos.iter_op Init.Nat.add p 1)%nat) by apply le_Pmult_nat.
    apply Peano.le_n_S; auto. }
  omega.
Qed.  

Lemma Pos2Nat_inj_2 : Pos.to_nat 2 = 2.
Proof. unfold Pos.to_nat; simpl; auto. Qed.

Lemma Pos_le_2_add_sub x : 
  (1 + (x - 1) <= 2 + (x - 2))%positive.
Proof.
  rewrite Pos2Nat.inj_le.
  rewrite !Pos2Nat.inj_add.
  assert (Pos.to_nat 1 = 1%nat) as -> by auto.
  assert (Pos.to_nat 2 = 2%nat) as -> by auto.
  destruct (Pos.ltb_spec x 1).
  { elimtype False.
    apply (Pos.nlt_1_r _ H). }
  destruct (Pos.eqb_spec x 1).
  { subst x.
    simpl.
    rewrite Pos.sub_le; auto. }
  assert (H2: Pos.compare_cont Eq x 1 = Gt).
  { rewrite Pos.compare_cont_spec.
    rewrite Pos.compare_antisym.
    rewrite <-Pos.leb_le in H.
    rewrite Pos.leb_compare in H.
    generalize H; clear H.
    destruct (Pos.compare 1 x) eqn:H; simpl; auto.
    { rewrite Pos.compare_eq_iff in H; subst x; elimtype False; auto. }
    inversion 1. }
  rewrite nat_of_P_minus_morphism; auto.
  destruct (Pos.ltb_spec x 2).
  { (*x=1*)
    elimtype False; apply n.
    rewrite Pos.le_lteq in H.
    destruct H; auto.
    rewrite Pos2Nat.inj_lt in H, H0.
    rewrite <-Pos2Nat.inj_iff.
    clear - H H0.
    rewrite Pos2Nat.inj_1 in H|-*.
    rewrite Pos2Nat_inj_2 in H0.
    omega. }
  destruct (Pos.eqb_spec x 2).
  { (*x=2*)
    subst x.
    simpl.
    omega. }
  assert (H3: Pos.compare_cont Eq x 2 = Gt).
  { apply nat_of_P_gt_Gt_compare_complement_morphism.
    rewrite Pos2Nat.inj_le in H, H0.
    rewrite Pos2Nat.inj_1 in H.
    rewrite Pos2Nat_inj_2 in H0|-*.
    assert (H1: Pos.to_nat x <> 2).
    { intros Hx.
      rewrite <-Pos2Nat.inj_iff, Hx in n0.
      auto. }
    omega. }
  rewrite nat_of_P_minus_morphism; auto.
  simpl.
  assert (Pos.to_nat 1 = 1%nat) as -> by auto.
  assert (Pos.to_nat 2 = 2%nat) as -> by auto.
  apply Peano.le_n_S.
  generalize (Pos.to_nat x) as m; intro.
  induction m; try solve[omega].
Qed.

Lemma Psize_minus_aux (x y : positive) : (x <= Pos.div2 (2^y) + (x - y))%positive.
Proof.
  revert y.
  apply Pos.peano_ind.
  { unfold Pos.pow, Pos.mul, Pos.iter, Pos.div2.
    apply Pos_le_1_add_sub. }
  intros p H.
  rewrite Pos.pow_succ_r; simpl.
  eapply Pos.le_trans; [apply H|].
  clear H.
  set (P := fun p =>
       forall x, (Pos.div2 (2 ^ p) + (x - p) <= 2 ^ p + (x - Pos.succ p))%positive).
  revert x.
  change (P p).
  apply Pos.peano_ind.
  { unfold P.
    intros x.
    unfold Pos.pow, Pos.mul, Pos.iter, Pos.div2.
    apply Pos_le_2_add_sub. }
  intros r; unfold P; simpl; intros IH x.
  rewrite Pos.pow_succ_r.
  unfold Pos.div2, Pos.mul.
  generalize (2^r)%positive as y; intro.
  generalize (Pos.succ r) as z; intro.
  assert (H: (x - z <= Pos.succ (x - Pos.succ z))%positive).
  { rewrite Pos.sub_succ_r.
    destruct (Pos.eqb_spec (x-z) 1).
    { rewrite e; simpl.
      rewrite Pos2Nat.inj_le, Pos2Nat.inj_1, Pos2Nat_inj_2; omega. }
    rewrite Pos.succ_pred; auto.
    apply Pos.le_refl. }
  generalize H.
  generalize (x - Pos.succ z)%positive as q; intro.
  clear IH H; intros H.
  set (Q := fun y => (y + (x - z) <= y~0 + q)%positive).
  change (Q y).
  apply Pos.peano_ind.
  { unfold Q.
    assert (2 + q = 1 + Pos.succ q)%positive as ->.
    { rewrite <-Pos.add_1_l, Pos.add_assoc; auto. }
    apply Pos.add_le_mono_l; auto. }
  intros t; unfold Q; intros IH.
  rewrite Pplus_one_succ_l.
  rewrite <-Pos.add_assoc.
  rewrite Pos.add_xO.
  rewrite <-Pos.add_assoc.  
  apply Pos.add_le_mono; auto.
  apply Pos.le_1_l.
Qed.

Lemma Psize_exp_div y : (Pos.div2 (2 ^ (Pos.size y)) <= y)%positive.
Proof.
  generalize (Pos.size_le y).
  destruct (2 ^ Pos.size y)%positive; simpl.
  { unfold Pos.le, Pos.compare; simpl.
    intros H H2.
    apply nat_of_P_gt_Gt_compare_morphism in H2.
    apply H.
    rewrite Pos.compare_cont_Gt_Gt.
    rewrite Pos2Nat.inj_ge; omega. }
  { unfold Pos.le, Pos.compare; simpl.
    intros H H2.
    apply H; auto. }
  intros _; apply Pos.le_1_l.
Qed.
  
Local Open Scope D_scope.

Lemma Dlub_mult_le1 d : d * Dlub d <= 1.
Proof.
  unfold Dle; rewrite Dmult_ok.
  unfold D_to_Q, Qle; destruct d as [x y]; simpl.
  rewrite Zmult_1_r; apply Zpos_2_mult.
  rewrite Pos2Z.inj_mul, !shift_pos_correct, !Zmult_1_r.
  rewrite <-Zpower_pos_is_exp.
  unfold Plub_aux.
  assert (H : (x <= Z.pow_pos 2 (Zsize x))%Z).
  { apply Zpow_pos_size_le. }
  eapply Zle_trans; [apply H|].
  rewrite <-!two_power_pos_correct.
  apply two_power_pos_le.
  rewrite Pos2Nat.inj_le; generalize (Zsize x) as z; intro.
  clear H.
  rewrite Pos2Nat.inj_add.
  destruct (Pos.ltb_spec y z) as [H|H].
  { rewrite Pos2Nat.inj_sub; auto.
    omega. }
  assert ((z - y = 1)%positive) as ->.
  { apply Pos.sub_le; auto. }
  revert H; rewrite Pos2Nat.inj_le.
  rewrite Pos2Nat.inj_1.
  omega.
Qed.

Lemma Dlub_nonneg (d : D) :
  0 <= d -> 0 <= Dlub d.
Proof.
  destruct d; simpl; intros H.
  unfold Dle; rewrite D_to_Q0; unfold D_to_Q; simpl.
  unfold Qle; simpl; omega.
Qed.

Lemma Dlub_ok (d : D) :
  0 <= d -> 
  Dle 0 (d * Dlub d) /\ Dle (d * Dlub d) 1.
Proof.
  intros H.
  split.
  { unfold Dle; rewrite Dmult_ok.
    rewrite D_to_Q0; apply Qmult_le_0_compat.
    { rewrite <-D_to_Q0; auto. }
    rewrite <-D_to_Q0; apply Dlub_nonneg; auto. }
  apply Dlub_mult_le1.
Qed.

Fixpoint Dred' (n : Z) (d : nat) : (Z * nat) :=
  match d with
  | O => (n,d)
  | S d' => if Zeven_dec n then Dred' (Z.div2 n) d'
            else (n,d)
  end.

Lemma Dred'P n d : Zodd (fst (Dred' n d)) \/ (snd (Dred' n d) = 0%nat).
Proof.
  revert n; induction d; auto.
  intros n; simpl; destruct (Zeven_dec n).
  { apply (IHd (Z.div2 n)). }
  left; simpl.
  destruct (Zodd_dec n); auto.
  destruct (Zeven_odd_dec n); auto.
  elimtype False; apply n0; auto.
Qed.  

Definition D_of_Dred' (p : Z*nat) : D :=
  let (x,y) := p in Dmake x (Pos.of_nat (S y)).

Definition Dred (d : D) : D := 
  D_of_Dred' (Dred' (num d) (pred (Pos.to_nat (den d)))).

Lemma DredP d : Zodd (num (Dred d)) \/ (den (Dred d) = 1%positive).
Proof.
  unfold Dred; destruct d as [x y]; simpl.
  destruct (Dred'P x (pred (Pos.to_nat y))).
  { unfold D_of_Dred'.
    destruct (Dred' _ _); auto. }
  destruct (Dred' _ _); right; simpl in *.
  rewrite H; auto.
Qed.  

Lemma D_of_Dred'_correct x y :
  D_to_Q (D_of_Dred' (Dred' x y)) == D_to_Q (D_of_Dred' (x,y)).
Proof.
  revert x; induction y.
  { intros x; apply Qeq_refl. }
  intros x.
  unfold Dred'; fold Dred'.
  destruct (Zeven_dec x) as [pf|pf].
  { rewrite IHy.
    unfold D_to_Q; simpl.
    unfold Qeq; simpl.
    pattern x at 2.
    rewrite (Zeven_div2 x pf).
    rewrite 2!shift_pos_correct, 2!Zmult_1_r.
    rewrite 2!Zpower_pos_nat.
    rewrite Pos2Nat.inj_succ.
    rewrite Zpower_nat_succ_r.
    rewrite Zmult_assoc.
    pattern (Z.div2 x * 2)%Z; rewrite Zmult_comm; auto. }
  apply Qeq_refl.
Qed.  

Lemma Dred_correct d : D_to_Q (Dred d) == D_to_Q d.
Proof.
  unfold Dred.
  destruct d as [x y] eqn:Heq.
  simpl.
  rewrite D_of_Dred'_correct.
  unfold D_of_Dred'.
  rewrite <-Pos.of_nat_succ.
  generalize (Pos2Nat.is_pos y).
  destruct (Pos.to_nat y) eqn:Heq'; try omega.
  intros _; simpl.
  rewrite (SuccNat2Pos.inv n y); auto.
  apply Qeq_refl.
Qed.  

Lemma gcd_2_odd_1 x : Zodd x -> Z.gcd x 2 = 1%Z.
Proof.
  generalize (Z.gcd_divide_r x 2).
  intros H.
  generalize (Znumtheory.Zdivide_bounds _ _ H).
  generalize (Z.gcd_nonneg x 2); intros H2 H3 H4.
  assert (H5: (Z.abs (Z.gcd x 2) <= Z.abs 2)%Z).
  { apply H3; inversion 1. }
  destruct (Z.abs_eq_iff (Z.gcd x 2)) as [_ Y].
  rewrite (Y H2) in H5. clear Y.
  simpl in H5.
  clear - H2 H4 H5.
  assert (H6: (Z.gcd x 2 = 0 \/ Z.gcd x 2 = 1 \/ Z.gcd x 2 = 2)%Z).
  { omega. }
  clear H2 H5.
  destruct H6.
  { apply Z.gcd_eq_0_l in H; subst x.
    inversion H4. }
  destruct H; auto.
  generalize (Z.gcd_divide_l x 2); rewrite H.
  intros H2; apply Znumtheory.Zdivide_mod in H2.
  rewrite Zmod_odd in H2.
  rewrite <-Zodd_bool_iff in H4; rewrite H4 in H2; inversion H2.
Qed.  

Lemma gcd_2_even_2 x : Zeven x -> Z.gcd x 2 = 2%Z.
Proof.
  generalize (Z.gcd_divide_r x 2).
  intros H.
  generalize (Znumtheory.Zdivide_bounds _ _ H).
  generalize (Z.gcd_nonneg x 2); intros H2 H3 H4.
  assert (H5: (Z.abs (Z.gcd x 2) <= Z.abs 2)%Z).
  { apply H3; inversion 1. }
  destruct (Z.abs_eq_iff (Z.gcd x 2)) as [_ Y].
  rewrite (Y H2) in H5. clear Y.
  simpl in H5.
  clear - H2 H4 H5.
  assert (H6: (Z.gcd x 2 = 0 \/ Z.gcd x 2 = 1 \/ Z.gcd x 2 = 2)%Z).
  { omega. }
  clear H2 H5.
  destruct H6.
  { apply Z.gcd_eq_0_l in H; subst x.
    auto. }
  destruct H; auto.
  elimtype False.
  rewrite Znumtheory.Zgcd_1_rel_prime in H.
  destruct H. 
  assert (H2: (2 | x)%Z).
  { apply Znumtheory.Zmod_divide.
    { inversion 1. }
    rewrite Zmod_odd.
    rewrite Zodd_even_bool.
    rewrite <-Zeven_bool_iff in H4; rewrite H4.
    auto. }
  assert (H3: (2 | 2)%Z).
  { exists 1%Z; auto. }
  assert (Hcontra: (2 | 1)%Z).
  { apply H1; auto. }
  assert (2 <= 1)%Z.
  { apply Z.divide_pos_le; auto.
    omega. }
  omega.
Qed.    

Lemma gcd_x_times2_1 x y : Zodd x -> Z.gcd x y = 1%Z -> Z.gcd x (2*y) = 1%Z.
Proof.
  intros Hodd H.
  generalize (Znumtheory.Zgcd_is_gcd x y) as H2; intro.
  apply Znumtheory.Zis_gcd_gcd; try omega.
  inversion H2.
  constructor; try apply Z.divide_1_l. 
  intros w H4 H5.
  rewrite H in H3.
  apply Znumtheory.Gauss in H5; auto.
  rewrite <-Znumtheory.Zgcd_1_rel_prime.
  destruct (Zeven_odd_dec w).
  { rewrite Zeven_ex_iff in z.
    destruct z as [m H6].
    rewrite H6 in H4.
    clear - Hodd H4.
    elimtype False.
    destruct H4 as [y H4].
    rewrite Zmult_assoc in H4.
    rewrite (Zmult_comm y) in H4.
    rewrite <-Zmult_assoc in H4.
    assert (H5: Zeven x).
    { rewrite H4.
      apply Zeven_2p. }
    apply Zodd_not_Zeven in Hodd; auto. }
  apply gcd_2_odd_1; auto.
Qed.  

Lemma gcd_pow2_odd_1 x n : Zodd x -> Z.gcd x (Zpower_nat 2 n) = 1%Z.
Proof.
  induction n.
  { simpl.
    rewrite Z.gcd_1_r; auto. }
  rewrite Zpower_nat_succ_r.
  intros Hodd.
  generalize (IHn Hodd).
  intros H.
  apply gcd_x_times2_1; auto.
Qed.  

Lemma Qred_odd_pow2 x n : Zodd x -> Qred (x # pow_pos 2 n) = x # (pow_pos 2 n).
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x ('pow_pos 2 n)).
  generalize (Z.ggcd_correct_divisors x ('pow_pos 2 n)).
  destruct (Z.ggcd x ('pow_pos 2 n)) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x ('pow_pos 2 n) = 1%Z).
  { rewrite pow_pos_Zpow_pos, Zpower_pos_nat.
    apply gcd_pow2_odd_1; auto. }
  rewrite H2, Zmult_1_l in H.
  subst c.
  rewrite H2, Zmult_1_l in H0.
  subst b.
  auto.
Qed.  

Lemma Qred_odd_2 x : Zodd x -> Qred (x # 2) = x # 2.
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x 2).
  generalize (Z.ggcd_correct_divisors x 2).
  destruct (Z.ggcd x 2) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x 2 = 1%Z).
  { apply gcd_2_odd_1; auto. }
  rewrite H2, Zmult_1_l in H.
  subst c.
  rewrite H2, Zmult_1_l in H0.
  subst b.
  auto.
Qed.  

Lemma shift_pos_pow_pos n : shift_pos n 1 = pow_pos 2 n.
Proof.
  rewrite shift_pos_nat.
  set (P := fun n => shift_nat (Pos.to_nat n) 1 = pow_pos 2 n).
  change (P n).
  apply Pos.peano_ind.
  { unfold P; auto. }
  intros p; unfold P; intros IH; simpl.
  rewrite Pos2Nat.inj_succ; simpl; rewrite IH.
  unfold pow_pos; simpl; auto.
  rewrite Pos.iter_succ; auto.
Qed.  

Lemma pow_pos_2inj p q : pow_pos 2 p = pow_pos 2 q -> p = q.
Proof.
  rewrite <-!shift_pos_pow_pos.
  unfold shift_pos.
  rewrite !Pos2Nat.inj_iter; intros H.
  apply Pos2Nat.inj.
  revert H.
  generalize (Pos.to_nat p) as n.
  generalize (Pos.to_nat q) as m.
  clear p q.
  induction m.
  { destruct n; auto. inversion 1. }
  destruct n; simpl.
  { inversion 1. }
  inversion 1; subst; f_equal; apply IHm; auto.
Qed.  

Lemma Qred_even_2 x :
  Zeven x -> 
  Qred (x # 2) = Z.div2 x # 1.
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x 2).
  generalize (Z.ggcd_correct_divisors x 2).
  destruct (Z.ggcd x 2) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x 2 = 2%Z).
  { apply gcd_2_even_2; auto. }
  rewrite H2 in H.
  assert (H4: c = 1%Z).
  { omega. }
  subst c.
  rewrite H2 in H0.
  rewrite H0.
  f_equal.
  destruct b; auto.
Qed.  

Lemma Zdiv2_even_inj x y : Zeven x -> Zeven y -> Z.div2 x = Z.div2 y -> x=y.
Proof.
  intros H H1 H2.
  destruct x; destruct y; simpl in H2; auto;
  try destruct p; try destruct p0; inversion H2;
  try inversion H; try inversion H1; auto.
Qed.  

Lemma Dred_complete d1 d2 :
  D_to_Q d1 == D_to_Q d2 ->
  Dred d1 = Dred d2.
Proof.
  generalize (Dred_correct d1). intros <-.
  generalize (Dred_correct d2). intros <-.
  intros H.
  apply Qred_complete in H.
  unfold D_to_Q in H|-*.
  generalize H; clear H.
  rewrite !shift_pos_pow_pos.
  destruct (DredP d1).
  (* Zodd (num (Dred d1)) *)
  { destruct (DredP d2).
    (* Zodd (num (Dred d2)) *)
    { rewrite !Qred_odd_pow2; auto.
      destruct (Dred d1); simpl.
      destruct (Dred d2); simpl.
      inversion 1; subst.
      f_equal.
      apply pow_pos_2inj; auto. }

    (* den (Dred d2) = 1 *)    
    rewrite H0.
    rewrite Qred_odd_pow2; auto.
    intros H2.
    assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
    rewrite Hpow in H2.
    destruct (Zeven_odd_dec (num (Dred d2))).
    { assert (Qred (num (Dred d2) # 2) = Z.div2 (num (Dred d2)) # 1).
      { rewrite Qred_even_2; auto. }
      rewrite H1 in H2; clear H1.
      inversion H2.
      assert (1 < pow_pos 2 (den (Dred d1)))%positive.
      { rewrite <-shift_pos_pow_pos.
        rewrite shift_pos_nat.
        destruct (Pos2Nat.is_succ (den (Dred d1))) as [x H1].
        rewrite H1; simpl.
        generalize (shift_nat x 1); intros p.
        unfold Pos.lt, Pos.compare; simpl; auto. }
      rewrite H4 in H1.
      inversion H1. }
    rewrite <-Hpow in H2.
    rewrite Qred_odd_pow2 in H2; auto.
    rewrite Hpow in H2.
    inversion H2; subst.
    revert H3 H4 H0.
    destruct (Dred d1); simpl.
    destruct (Dred d2); simpl.
    intros -> Hx ->.
    assert (Hy: pow_pos 2 1 = pow_pos 2 den0).
    { rewrite Hx, Hpow; auto. }
    f_equal.
    apply pow_pos_2inj; auto. }

  (* den (Dred d1) = 1 *)    
  destruct (DredP d2).
    (* Zodd (num (Dred d2)) *)
    { rewrite H.
      rewrite (Qred_odd_pow2 _ _ H0).
      intros H2.
      assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
      rewrite Hpow in H2.
      destruct (Zeven_odd_dec (num (Dred d1))).
      { assert (Qred (num (Dred d1) # 2) = Z.div2 (num (Dred d1)) # 1).
        { rewrite Qred_even_2; auto. }
        rewrite H1 in H2; clear H1.
        inversion H2.
        assert (1 < pow_pos 2 (den (Dred d2)))%positive.
        { rewrite <-shift_pos_pow_pos.
          rewrite shift_pos_nat.
          destruct (Pos2Nat.is_succ (den (Dred d2))) as [x H1].
          rewrite H1; simpl.
          generalize (shift_nat x 1); intros p.
          unfold Pos.lt, Pos.compare; simpl; auto. }
        rewrite <-H4 in H1.
        inversion H1. }
      rewrite <-Hpow in H2.
      rewrite Qred_odd_pow2 in H2; auto.
      rewrite Hpow in H2.
      inversion H2; subst.
      revert H3 H4 H0.
      destruct (Dred d2); simpl.
      destruct (Dred d1); simpl.            
      intros <- Hx Hodd.
      simpl in H.
      subst den1.
      assert (Hy: pow_pos 2 1 = pow_pos 2 den0).
      { rewrite <-Hx, Hpow; auto. }
      f_equal.
      apply pow_pos_2inj; auto. }

    (* den (Dred d1) = 1 *)
    rewrite H, H0.
    assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
    rewrite Hpow.
    destruct (Dred d1) as [num1 den1].
    destruct (Dred d2) as [num2 den2].
    destruct (Zeven_odd_dec num1); destruct (Zeven_odd_dec num2).
    { rewrite !Qred_even_2; auto.
      simpl.
      inversion 1; subst.
      apply Zdiv2_even_inj in H3; auto.
      subst num1.
      simpl in H0, H.
      subst; auto. }
    { rewrite Qred_even_2; auto.
      rewrite Qred_odd_2; auto.
      simpl.
      inversion 1. }
    { rewrite Qred_odd_2; auto.
      rewrite Qred_even_2; auto.
      simpl.
      inversion 1. }
    rewrite !Qred_odd_2; auto.
    inversion 1; subst.
    simpl in H0, H; subst; auto. 
Qed.

Lemma Dred'_idem x y :
  Dred' (fst (Dred' x y)) (snd (Dred' x y)) = Dred' x y.
Proof.
  destruct (Dred'P x y).
  { revert H.
    generalize (Dred' x y).
    destruct p.
    simpl; intros H.
    unfold Dred'.
    destruct n; auto.
    destruct (Zeven_dec z); auto.
    apply Zodd_not_Zeven in H; contradiction. }
  destruct (Dred' x y); simpl in H|-*; rewrite H; auto.
Qed.  
    
Lemma Dred_idem d : Dred (Dred d) = Dred d.
Proof.
  unfold Dred.
  destruct (Dred' _ _) eqn:H.
  unfold D_of_Dred' in H.
  assert (H2: (num
           (let (x, y) :=
              Dred' (num d) (Init.Nat.pred (Pos.to_nat (den d))) in
            {| num := x; den := Pos.of_nat (S y) |})) =
              fst (Dred' (num d) (Init.Nat.pred (Pos.to_nat (den d))))).
  { destruct (Dred' _ _).
    destruct (Dred' _ _); auto. }
  rewrite H2 in H.
  assert (H3: (Init.Nat.pred
           (Pos.to_nat
              (den
                 (let (x, y) :=
                    Dred' (num d) (Init.Nat.pred (Pos.to_nat (den d))) in
                  {| num := x; den := Pos.of_nat (S y) |})))) =
              snd (Dred' (num d) (Init.Nat.pred (Pos.to_nat (den d))))).
  { destruct (Dred' _ _).
    destruct (Dred' _ _); auto.
    simpl.
    destruct n1; auto.
    rewrite Pos2Nat.inj_succ.
    unfold Init.Nat.pred.
    rewrite Nat2Pos.id; auto. }
  rewrite H3 in H.
  rewrite Dred'_idem in H.
  rewrite H; auto.
Qed.  

Module DRed.
  Record t : Type :=
    mk { d :> D;
         pf : Dred d = d }.

  Definition build (d : D) : t := @mk (Dred d) (Dred_idem d).
  
  Program Definition t0 := mk 0 _.

  Program Definition t1 := mk 1 _.
  
  Program Definition add (d1 d2 : t) : t :=
    mk (Dred (Dadd d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_complete; rewrite Dred_correct; apply Qeq_refl.
  Qed.

  Program Definition sub (d1 d2 : t) : t :=
    mk (Dred (Dsub d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_complete; rewrite Dred_correct; apply Qeq_refl.    
  Qed.

  Program Definition mult (d1 d2 : t) : t := 
    mk (Dred (Dmult d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_complete; rewrite Dred_correct; apply Qeq_refl.        
  Qed.

  Program Definition opp (dx : t) : t := 
    mk (Dred (Dopp dx.(d))) _.
  Next Obligation.
    apply Dred_complete; rewrite Dred_correct; apply Qeq_refl.            
  Qed.

  Program Definition lub (dx : t) : t := 
    mk (Dred (Dlub dx.(d))) _.
  Next Obligation.
    apply Dred_complete; rewrite Dred_correct; apply Qeq_refl.            
  Qed.

  Lemma Dred_eq (d1 d2 : t) : (D_to_Q (d d1) == D_to_Q (d d2))%Q -> d1 = d2.
  Proof.
    destruct d1 as [x1 pf1]; destruct d2 as [x2 pf2]; simpl.
    intros H; assert (H2: x1 = x2).
    { rewrite <-pf1, <-pf2; apply Dred_complete; auto. }
    generalize pf1 pf2; rewrite H2; intros; f_equal; apply proof_irrelevance.
  Qed.    
  
  Lemma addP d1 d2 :
    D_to_Q (d (add d1 d2)) == (D_to_Q (d d1) + D_to_Q (d d2))%Q.
  Proof.
    unfold add; simpl.
    rewrite Dred_correct.
    rewrite Dadd_ok; apply Qeq_refl.
  Qed.    
  
  Lemma addC d1 d2 : add d1 d2 = add d2 d1.
  Proof.
    apply Dred_eq; simpl; rewrite 2!Dred_correct, 2!Dadd_ok.
    apply Qplus_comm.
  Qed.

  Lemma addA d1 d2 d3 : add d1 (add d2 d3) = add (add d1 d2) d3.
  Proof.
    apply Dred_eq; simpl.
    rewrite !Dred_correct, !Dadd_ok, !Dred_correct, !Dadd_ok.
    apply Qplus_assoc.
  Qed.    

  Lemma add0l d : add t0 d = d.
  Proof.
    unfold t0; apply Dred_eq; unfold add.
    generalize (add_obligation_1 {|d:=0;pf:=t0_obligation_1|} d).
    unfold DRed.d; rewrite Dred_correct; intros e.
    rewrite Dadd_ok, D_to_Q0, Qplus_0_l; apply Qeq_refl.
  Qed.    
        
  Lemma subP d1 d2 :
    D_to_Q (d (sub d1 d2)) == (D_to_Q (d d1) - D_to_Q (d d2))%Q.
  Proof.
    unfold sub; simpl.
    rewrite Dred_correct.
    rewrite Dsub_ok; apply Qeq_refl.
  Qed.

  Lemma multP d1 d2 :
    D_to_Q (d (mult d1 d2)) == (D_to_Q (d d1) * D_to_Q (d d2))%Q.
  Proof.
    unfold mult; simpl.
    rewrite Dred_correct.
    rewrite Dmult_ok; apply Qeq_refl.
  Qed.    
  
  Lemma multC d1 d2 : mult d1 d2 = mult d2 d1.
  Proof.
    apply Dred_eq; simpl; rewrite 2!Dred_correct, 2!Dmult_ok.
    apply Qmult_comm.
  Qed.

  Lemma multA d1 d2 d3 : mult d1 (mult d2 d3) = mult (mult d1 d2) d3.
  Proof.
    apply Dred_eq; simpl.
    rewrite !Dred_correct, !Dmult_ok, !Dred_correct, !Dmult_ok.
    apply Qmult_assoc.
  Qed.    

  Lemma oppP dx :
    D_to_Q (d (opp dx)) == (- D_to_Q (d dx))%Q.
  Proof.
    unfold opp; simpl.
    rewrite Dred_correct.
    rewrite Dopp_ok; apply Qeq_refl.
  Qed.

  Lemma lubP (dx : t) :
    0 <= dx -> 0 <= dx * lub dx /\ dx * lub dx <= 1.
  Proof.
    intros H.
    generalize (Dlub_ok dx H); intros [H1 H2].
    unfold lub, Dle in *; simpl.
    rewrite Dmult_ok in *.
    rewrite Dred_correct in *; auto.
  Qed.

  (* TODO: More lemmas here! *)
End DRed.      

Coercion DRed.d : DRed.t >-> D.

Delimit Scope DRed_scope with DRed.
Bind Scope DRed_scope with DRed.t.

(* notations repeated from D_scope *)
Infix "<" := Dlt : DRed_scope.
Infix "<=" := Dle : DRed_scope.
Notation "x > y" := (Dlt y x)(only parsing) : DRed_scope.
Notation "x >= y" := (Dle y x)(only parsing) : DRed_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : DRed_scope.
(* END *)

Infix "+" := DRed.add : DRed_scope.
Notation "- x" := (DRed.opp x) : DRed_scope.
Infix "-" := DRed.sub : DRed_scope.
Infix "*" := DRed.mult : DRed_scope.

Notation "'0'" := DRed.t0 : DRed_scope.
Notation "'1'" := DRed.t1 : DRed_scope.


  
  
  

  
  
    
                         
