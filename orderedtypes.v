Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ProofIrrelevance.
Require Import String.
Require Import QArith.
Require Import Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import strings compile numerics dyadic.
Require Import listlemmas maplemmas.
(* Boolability is important to our construction of affine games,
      however, it is non-essential and problematic for more advanced
      games (e.g. the routing games shown in routing.v)

  It's not hard to preserve boolability with certain combinators,
  however, it is hard to regain it.

  To work around this we have two layers of modules here:
    1.) MyOrderedType, used to preserve Boolablity through particular combinators.
    2.) SimpleMyOrderedType, used to strip away Boolability
          and its associated requirements
*)

(* Define the basic extension of OrderedType: MyOrderedType *)
Module Type MyOrderedType.
  Parameter t : Type.
  Parameter t0 : t.
  Parameter enumerable : Enumerable t.
  Parameter showable : Showable t.
  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter eqP : forall x y, x = y <-> eq x y.
End MyOrderedType.

Module OrderedType_of_MyOrderedType (A : MyOrderedType)
  <: OrderedType.OrderedType.
      Definition t : Type := A.t.
      Definition eq := A.eq.
      Definition lt := A.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. by move => x; rewrite /eq -A.eqP. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. by move => x y; rewrite /eq -2!A.eqP. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. by move => x y z; rewrite /eq -3!A.eqP => -> ->. Qed.
      Definition lt_trans := A.lt_trans.
      Definition lt_not_eq := A.lt_not_eq.
      Definition compare := A.compare.
      Definition eq_dec := A.eq_dec.
End OrderedType_of_MyOrderedType.

Module Type OrderedFinType.
  Include MyOrderedType.
  Parameter eq_mixin : Equality.mixin_of t.
  Parameter choice_mixin : Choice.mixin_of (EqType t eq_mixin).
  Parameter fin_mixin : Finite.mixin_of (ChoiceType (EqType t eq_mixin) choice_mixin).
End OrderedFinType.

Module MyOrderedType_of_OrderedFinType
       (A : OrderedFinType) <: MyOrderedType.
  Include A.                                
End MyOrderedType_of_OrderedFinType.

(* We now begin defining functors for constructing
    OrderedTypes and BoolableOrderedTypes *)

(** First, we set up those functors which work without boolability **)

  (* Products and their extensions (boolable and fin) *)
Module OrderedProd (A B : MyOrderedType) <: MyOrderedType.
  Definition t := (A.t*B.t)%type.
  Definition t0 := (A.t0, B.t0).
  Definition enumerable  : Enumerable t := _.
  Definition show_prod (p : A.t*B.t) : string :=
    let s1 := to_string p.1 in
    let s2 := to_string p.2 in
    append s1 s2.
  Instance showable : Showable t := mkShowable show_prod.
  Definition eq p1 p2 : Prop :=
    (eqProd A.eq B.eq) p1 p2.
  Definition lt p1 p2 :=
    match p1, p2 with
    | (a1, b1), (a2, b2) =>
      A.lt a1 a2 \/
      (A.eq a1 a2 /\ B.lt b1 b2)
    end.
  
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    case => a b; case => c d; case => e f; rewrite /lt.
    case => H.
    { case => H1.
      { left; by apply: (A.lt_trans _ _ _ H H1). }
      case: H1 => H2 H3.
      by move: H2; rewrite -A.eqP => H4; subst e; left. }
    case: H; rewrite -A.eqP => H1 H2; subst c.
    case; first by move => H3; left.
    case => H3 H4; right; split => //.
    by apply: (B.lt_trans _ _ _ H2 H4).
  Qed.      

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    case => a b; case => c d; rewrite /lt /eq /=.
    case.
    { move => H []H2 H3.
        by apply: (A.lt_not_eq _ _ H). }
    case => H H1 []H2 H3.
    by apply: (B.lt_not_eq _ _ H1).
  Qed.
  
  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    move => x y.
    case H: (A.compare x.1 y.1) => [lt_pf|eq_pf|gt_pf].
    { have H2: lt x y.
      { clear - lt_pf.
        move: lt_pf; case: x => a b; case: y => c d /= H.
          by left. }
      apply: LT H2. }
    { case: (B.compare x.2 y.2) => [lt_pf'|eq_pf'|gt_pf'].
      { have H2: lt x y.
        { clear - eq_pf lt_pf'.
          move: eq_pf lt_pf'; case: x => a b; case: y => c d /= H H2.
          right; split => //. }
        apply: LT H2. }
      { have H2: eq x y.
        { rewrite /eq /eqProd. destruct x, y; split => //. }
        apply: EQ H2. }
      have H2: lt y x.
      { clear - eq_pf gt_pf'; move: eq_pf gt_pf'.
        case: x => a b; case: y => c d /= H H2.
        right; split => //.
        by move: H; rewrite -2!A.eqP => ->. }
      by apply: GT H2. }
    have H2: lt y x.
    { clear - gt_pf; move: gt_pf; case: x => a b; case: y => c d /= H.
      by left. }
    by apply: GT H2.    
  Qed.        

  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}.
  Proof.
    case => a b; case => c d; rewrite /eq /=.
    case H2: (A.eq_dec a c) => [pf|pf].
    { case H3: (B.eq_dec b d) => [pf'|pf'].
      { left.
        split => //. }
      right.
      case => H4 H5.
      clear H2 H3.
        by apply: pf'. }
    right; case => H3 H4.
    by clear H2; apply: pf.
  Qed.    

  Lemma eqP : forall x y, x = y <-> eq x y.
  Proof.
    case => a b; case => c d; rewrite /eq /=; split.
    { case => -> ->; split.
        by rewrite -A.eqP.
        by rewrite -B.eqP. }
    by case; rewrite -A.eqP -B.eqP => -> ->.
  Qed.
End OrderedProd.

Module OrderedFinProd (X Y : OrderedFinType) <: OrderedFinType.
  Module A := OrderedProd X Y. 
  Include A.
  
  Definition xE := EqType X.t X.eq_mixin.
  Definition xC := ChoiceType xE X.choice_mixin.
  Definition xF := FinType xC X.fin_mixin.

  Definition yE := EqType Y.t Y.eq_mixin.
  Definition yC := ChoiceType yE Y.choice_mixin.
  Definition yF := FinType yC Y.fin_mixin.
  
  Definition eq_mixin := prod_eqMixin xE yE.
  Definition choice_mixin := prod_choiceMixin xC yC.
  Definition fin_mixin := prod_finMixin xF yF.
End OrderedFinProd.

(** MyOrdNatDep: a computational analogue of 'I_B.n *)

Module MyOrdNatDep (B : BOUND) <: MyOrderedType.
  Module N := OrdNatDep B. Include N.

  Program Definition t0 := @mk 0%N _.
  Next Obligation. by apply: B.n_gt0. Qed.

  (* FIXME: this definition should be fold_left, not fold_right *)
  Program Fixpoint enumerate_rec (m : nat) (pf : (m < n)%nat) : list t :=
    (match m as x return _ = x -> list t with
     | O => fun _ => t0 :: nil
     | S m' => fun pf => @mk (N.of_nat m) _ :: enumerate_rec m' _
     end) erefl.
  Next Obligation. by rewrite Nat2N.id. Qed.

  Lemma lt_dec x y : ({x<y} + {x>=y})%nat.
  Proof.
    case H: (leq (S x) y); first by left.
    case H2: (y <= x)%nat; first by right.
    move: (leq_total y x); rewrite H2 /= => H3.
    rewrite ltnNge in H.    
    rewrite leqNgt in H2.
    rewrite leqNgt in H3.
    rewrite -ltnNge in H.
    by rewrite H in H2.
  Qed.

  Lemma gt0_pred_lt n : (0 < n -> n.-1 < n)%nat.
  Proof. elim: n => //. Qed.
  
  Definition enumerate_t : list t :=
    match lt_dec 0 n with 
    | left pfn => enumerate_rec (Nat.pred n) (gt0_pred_lt _ pfn)
    | right _ => nil
    end.

  Instance enumerable : Enumerable t := enumerate_t.

  Instance showable : Showable t :=
    mkShowable (fun x => to_string x.(val)).

  Lemma eqP : forall x y : t, x = y <-> eq x y.
  Proof.
    move => x y; case: x => vx px; case y => vy py.
    rewrite /eq /=; split.
    { inversion 1; subst.
      apply: M.E.eq_refl. }
    rewrite /BinNat.N.eq => H; subst vy.
    f_equal.
    apply: proof_irrelevance.
  Qed.
End MyOrdNatDep.  
  
Module MyOrdNatDepProps (B : BOUND).
  Module M := MyOrdNatDep B. Include M.

  Fixpoint enumerate_rec_erased (m : nat) : list N :=
    match m with
    | O => N.of_nat O :: nil
    | S m' => N.of_nat m :: enumerate_rec_erased m'
    end.

  Lemma enumerate_rec_map_erased m (pf : (m < n)%nat) :
    map val (enumerate_rec m pf) = enumerate_rec_erased m.
  Proof. by elim: m pf => // n IH pf /=; f_equal; rewrite IH. Qed.

  Fixpoint enumerate_rec_erased_nat (m : nat) : list nat :=
    match m with
    | O => O :: nil
    | S m' => m :: enumerate_rec_erased_nat m'
    end.

  Lemma enumerate_rec_erased_nat_iota n :
    List.rev (enumerate_rec_erased_nat n) = iota 0 (n.+1).
  Proof.
    elim: n => // n /= ->.
    have ->: (0::iota 1 n = [::0]++iota 1 n)%nat by [].
    rewrite -app_assoc /=; f_equal.
    have ->: (n.+1 = n+1)%nat by rewrite addnC.
    move: 1%nat => nx; elim: n nx => //= n IH nx; f_equal.
    have ->: (n.+1 +nx = n + nx.+1)%nat by rewrite addSn.
    apply: IH.
  Qed.    
  
  Lemma enumerate_rec_map_erased_nat m :
    map N.to_nat (enumerate_rec_erased m) = enumerate_rec_erased_nat m.
  Proof.
    elim: m => // m IH /=; f_equal => //.
    by rewrite SuccNat2Pos.id_succ.
  Qed.      

  Lemma notin_gtn m n :
    (m > n)%nat -> 
    ~InA (fun x : nat => [eta Logic.eq x]) m (enumerate_rec_erased_nat n).
  Proof.
    elim: n m.
    { move => m H H2; inversion H2; subst => //.
      inversion H1. }
    move => n IH m H H2; apply: IH.
    { apply: ltn_trans; last by apply: H.
      by []. }
    inversion H2; subst => //.
    move: (ltP H) => H3; omega.
  Qed.    
  
  Lemma enumerate_rec_erased_nat_nodup m :
    NoDupA (fun x : nat => [eta Logic.eq x]) (enumerate_rec_erased_nat m).
  Proof.
    elim: m.
    { constructor; first by inversion 1.
      constructor. }
    move => n IH /=; constructor => //.
    by apply: notin_gtn.
  Qed.

  Lemma enumerate_rec_erased_nat_total n m :
    (n <= m)%nat ->
    In n (enumerate_rec_erased_nat m).
  Proof.
    elim: m n; first by case => //= _; left.
    move => m IH n H; case: (Nat.eq_dec n m.+1) => [pf|pf].
    { by left; subst n. }
    right; apply: IH.
    apply/leP; move: (leP H) => H2; omega.
  Qed.

  Lemma enumerate_rec_erased_total n m :
    (N.to_nat n <= N.to_nat m)%nat ->
    In n (enumerate_rec_erased (N.to_nat m)).
  Proof.
    move => H.
    suff: In (N.to_nat n) (map N.to_nat (enumerate_rec_erased (N.to_nat m))).
    { clear H; elim: m n.
      { move => n /=; case => // H; left.
        destruct n => //.
        simpl in H.
        move: (PosN0 p); rewrite -H //. }
      move => p n; rewrite in_map_iff; case => x []H H1.
      by move: (N2Nat.inj _ _ H) => H2; subst n. }
    rewrite enumerate_rec_map_erased_nat.
    apply: (enumerate_rec_erased_nat_total _ _ H).
  Qed.    

  Lemma enumerate_rec_total m (pf : (m < n)%nat) (x : t) :
    (m.+1 = n)%nat -> 
    In x (enumerate_rec _ pf).
  Proof.
    move => Hsucc.
    suff: In (val x) (map val (enumerate_rec m pf)).
    { clear Hsucc.
      elim: m pf x => /=.
      { move => H x; case => // H2; left.
        rewrite /t0; f_equal; destruct x as [vx pfx].
        simpl in H2; subst vx; f_equal.
        apply: proof_irrelevance. }
      move => n IH pf x; case.
      { destruct x as [vx pfx]; simpl => H; subst vx; left.
        f_equal.
        apply: proof_irrelevance. }
      rewrite in_map_iff; case => x0 [] H H2; right.
      clear - H H2.
      destruct x0 as [vx0 pfx0].
      destruct x as [vx pfx].
      simpl in H; subst vx0.
      have ->: pfx = pfx0 by apply: proof_irrelevance.
      by []. }
    rewrite enumerate_rec_map_erased.
    destruct x as [vx pfx].
    rewrite /val.
    have ->: m = N.to_nat (N.of_nat m) by rewrite Nat2N.id.
    apply: enumerate_rec_erased_total.
    rewrite Nat2N.id.
    apply/leP; move: (ltP pfx) (ltP pf); move: (N.to_nat vx) => n0.
    rewrite -Hsucc => X Y.
    omega.
  Qed.    
  
  Lemma InA_map A B (f : A -> B) (l : list A) x :
    InA (fun x => [eta Logic.eq x]) x l -> 
    InA (fun x => [eta Logic.eq x]) (f x) (map f l).
  Proof.
    elim: l; first by inversion 1.
    move => a l IH; inversion 1; subst; first by constructor.
    by apply: InA_cons_tl; apply: IH.
  Qed.
  
  Lemma enumerate_rec_erased_nodup m :
    NoDupA (fun x => [eta Logic.eq x]) (enumerate_rec_erased m).
  Proof.
    suff: (NoDupA (fun x => [eta Logic.eq x]) (map N.to_nat (enumerate_rec_erased m))).
    { elim: (enumerate_rec_erased m) => // a l IH; inversion 1; subst.
      constructor.
      { by move => H; apply: H1; apply: InA_map. }
      apply: (IH H2). }
    rewrite enumerate_rec_map_erased_nat.
    apply: enumerate_rec_erased_nat_nodup.
  Qed.      

  Lemma enumerate_rec_nodup m pf :
    NoDupA (fun x : t => [eta Logic.eq x]) (enumerate_rec m pf).
  Proof.
    suff: NoDupA (fun x => [eta Logic.eq x]) (map val (enumerate_rec m pf)).
    { elim: (enumerate_rec m pf) => // a l IH; inversion 1; subst.
      constructor.
      { clear - H1 => H2; apply: H1.
        elim: l H2; first by inversion 1.
        move => b l H; inversion 1; subst; first by constructor.
        by apply: InA_cons_tl; apply: H. }
      by apply: IH. }
    rewrite enumerate_rec_map_erased.
    apply: enumerate_rec_erased_nodup.
  Qed.

  Lemma enumerate_t_nodup :
    NoDupA (fun x : t => [eta Logic.eq x]) enumerate_t.
  Proof.
    rewrite /enumerate_t.
    case H: (lt_dec 0 n) => [pf|pf]; last by constructor.
    by apply: enumerate_rec_nodup.
  Qed.

  Lemma enumerate_t_total x : In x enumerate_t.
  Proof.
    rewrite /enumerate_t.
    case: (lt_dec 0 n) => [pf|pf]; last first.
    { destruct x as [vx pfx].
      move: (ltP pfx) (leP pf) => X Y.
      omega. }
    have H: (n = n.-1.+1).
    { rewrite (ltn_predK (m:=0)) => //. }
    symmetry in H.
    by apply: (enumerate_rec_total _ (gt0_pred_lt n pf) x H).
  Qed.

  Program Instance enum_ok : @Enum_ok t enumerable.
  Next Obligation.
    rewrite /enumerable_fun /enumerable.
    apply: enumerate_t_nodup.
  Qed.
  Next Obligation.
    rewrite /enumerable_fun /enumerable.
    apply: enumerate_t_total.
  Qed.

  Definition Ordinal_of_t (x : t) :=
    @Ordinal n (N.to_nat (val x)) (M.pf x).

  Definition val_of_Ordinal (x : 'I_n) : N :=
    match x with
      Ordinal n _ => N.of_nat n
    end.
  
  Lemma rev_enumerate_enum :
    List.rev (List.map Ordinal_of_t enumerate_t) =
    enum 'I_n.
  Proof.
    rewrite /enumerate_t; case: (lt_dec 0 n); last first.
    { move => a; move: (leP a) => H; move: (ltP B.n_gt0) => Hx; omega. }
    move => pf.
    suff: (List.rev (map val (enumerate_rec n.-1 (gt0_pred_lt n pf))) =
           List.map val_of_Ordinal (enum 'I_n)).
    { move: (enumerate_rec _ _) => l1.
      move: (enum 'I_n) => l2; elim: l1 l2; first by case.
      move => a l1 /= IH l2 H2.
      have [l2' H]:
        exists l2',
          map val_of_Ordinal l2 = map val_of_Ordinal l2' ++ [:: val a].
      { clear - H2; move: H2; move: (rev _) => l1x.
        elim: l2 l1x => //.
        { move => l1x /=; case: l1x => //. }
        move => ax l2x IH l1x /= H2; case: l1x H2.
        { simpl; inversion 1; subst; exists nil => //. }
        move => ay l1y /=; inversion 1; subst.
        case: (IH _ H1) => ll H3; exists (ax :: ll); simpl.
        by rewrite -H1 in H3; rewrite H3. }
      rewrite H in H2; apply app_inj_tail in H2; case: H2 => H2 _.
      rewrite (IH _ H2); clear - H; symmetry in H.
      have H2:
        map val_of_Ordinal l2' ++ [:: val a] =
        map val_of_Ordinal (l2' ++ [:: Ordinal_of_t a]).
      { by rewrite map_app /= N2Nat.id. }
      rewrite H2 in H; clear H2.
      apply: map_inj; last by apply: H.
      move => x y; case: x => x pfx; case: y => y pfy; move/Nat2N.inj.
      move => H2; subst; f_equal; apply: proof_irrelevance. }
    rewrite enumerate_rec_map_erased.
    suff:
      rev (map N.to_nat (enumerate_rec_erased n.-1)) =
      map N.to_nat (map val_of_Ordinal (enum 'I_n)).
    { rewrite -map_rev; move/map_inj; apply; apply: N2Nat.inj. }
    rewrite enumerate_rec_map_erased_nat.
    rewrite enumerate_rec_erased_nat_iota.
    have ->: (map N.to_nat (map val_of_Ordinal (enum 'I_n)) = iota 0 n).
    { have ->:
        map N.to_nat (map val_of_Ordinal (enum 'I_n)) =
        map eqtype.val (enum 'I_n).
      { elim: (enum 'I_n) => // a l /= IH; f_equal => //.
        by case: a => // m i; rewrite /val_of_Ordinal Nat2N.id. }
      rewrite -val_enum_ord //. }
    have ->: (n.-1.+1 = n).
    { move: (ltP pf) => Hx; omega. }
    by [].
  Qed.
End MyOrdNatDepProps.
