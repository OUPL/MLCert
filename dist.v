Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import bigops.

Local Open Scope ring_scope.

(** Discrete distributions *)

Section Dist.
  Variable T : finType.
  Variable rty : numDomainType.

  Definition dist_axiom (f : {ffun T -> rty}) :=
    [&& \sum_t (f t) == 1
      & [forall t : T, f t >= 0]].
  Record dist : Type := mkDist { pmf :> {ffun T -> rty}; dist_ax : dist_axiom pmf }.
  Canonical dist_subType := [subType for pmf].

  (* We have eqType and choiceTypes on distributions:*)
  Definition dist_eqMixin := Eval hnf in [eqMixin of dist by <:].
  Canonical dist_eqType := Eval hnf in EqType dist dist_eqMixin.
  Definition dist_choiceMixin := [choiceMixin of dist by <:].
  Canonical dist_choiceType := Eval hnf in ChoiceType dist dist_choiceMixin.
End Dist.

Section distLemmas.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Lemma dist_normalized : \sum_t d t = 1.
  Proof. by case: (andP (dist_ax d)); move/eqP. Qed.

  Lemma dist_positive : forall t : T, d t >= 0.
  Proof. by case: (andP (dist_ax d))=> _; move/forallP. Qed.
End distLemmas.

Section support.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition support : {set T} := [set t : T | 0 < d t].

  Lemma in_support x : x \in support -> 0 < d x.
  Proof. by rewrite /support in_set. Qed.

  Lemma supportP x : x \in support <-> 0 < d x.
  Proof.
    split; first by apply: in_support.
    by rewrite /support in_set.
  Qed.      
End support.

Section bind.
  Variable T U : finType.
  Variable rty : numDomainType.  
  Variable d : {ffun T -> rty}.
  Variable f : T -> {ffun U -> rty}.
  Definition bind : {ffun U -> rty} :=
    finfun (fun u : U => \sum_(t : T) (d t) * (f t u)).
End bind.
  
Section expectedValue.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition probOf (p : pred T) :=
      \sum_(t : T | p t) d t.

  Lemma probOf_xpredT : probOf xpredT = 1.
  Proof.
    rewrite /probOf; apply: dist_normalized.
  Qed.

  Lemma probOf_nonneg (p : pred T) : 0 <= probOf p.
  Proof.
    apply: sumr_ge0 => i Hi; apply: dist_positive.
  Qed.    

  Definition expectedCondValue (f : T -> rty) (p : pred T) :=
    (\sum_(t : T | p t) (d t) * (f t)) / (probOf p).

  Lemma expectedCondValue_mull f p c :
    expectedCondValue (fun t => c * f t) p = c * expectedCondValue f p.
  Proof.
    rewrite /expectedCondValue.
    have ->: \sum_(t | p t) d t * (c * f t)
           = c * \sum_(t | p t) d t * f t.
    { rewrite mulr_sumr; apply/congr_big=> //= i _.
      by rewrite mulrA [d i * c]mulrC -mulrA. }
    by rewrite mulrA.
  Qed.

  Lemma expectedCondValue_linear f g p :
    expectedCondValue (fun t => f t + g t) p =
    expectedCondValue f p + expectedCondValue g p.
  Proof.
    rewrite /expectedCondValue.
    have ->: \sum_(t | p t) d t * (f t + g t) =
             \sum_(t | p t) (d t * f t + d t * g t).
    { by apply/congr_big=> //= i _; rewrite mulrDr. }
    rewrite 3!mulr_suml -big_split /=; move: (probOf p) => e.
    apply: congr_big => // i _; rewrite mulrDl //.
  Qed.    

  Lemma sum_split (f : T -> rty) p :
    \sum_t f t = \sum_(t | p t) f t + \sum_(t | ~~p t) f t.
  Proof.
    have ->: \sum_t f t = \sum_(t | p t || ~~p t) f t.
    { by apply/congr_big => // x; case: (p x). }
    rewrite -big_filter.
    have ->:
      \sum_(i <- [seq i <- index_enum T | p i || ~~ p i]) f i
    = \sum_(i <- [seq i <- index_enum T | p i] ++ [seq i <- index_enum T | ~~p i]) f i.
    { apply: eq_big_perm.
      have ->: [seq i <- index_enum T | ~~ p i] = [seq i <- index_enum T | predC p i] by [].
      rewrite perm_eq_sym perm_filterC.
      have ->: [seq i <- index_enum T | p i || ~~ p i] = index_enum T.
      { have ->: [seq i <- index_enum T | p i || ~~ p i] = [seq i <- index_enum T | predT i].
        { by apply eq_in_filter => x; rewrite /in_mem /= => H; case: (p x). }
        by rewrite filter_predT. }
      by []. }
    by rewrite big_cat /= !big_filter.
  Qed.    
  
  Definition expectedValue (f : T -> rty) :=
    \sum_(t : T) (d t) * (f t).

  Lemma expectedValue_split f p :
    expectedValue f = \sum_(t | p t) d t * f t + \sum_(t | ~~p t) d t * f t.
  Proof.
    rewrite /expectedValue; rewrite ->sum_split with (p:=p); f_equal => //.
  Qed.    
  
  Lemma expectedValue_expectedCondValue f : 
    expectedValue f = expectedCondValue f xpredT.
  Proof.
    by rewrite /expectedValue /expectedCondValue probOf_xpredT divr1.
  Qed.
  
  Lemma expectedValue_mull f c :
    expectedValue (fun t => c * f t) = c * expectedValue f.
  Proof. by rewrite 2!expectedValue_expectedCondValue expectedCondValue_mull. Qed.

  Lemma expectedValue_linear f g :
    expectedValue (fun t => f t + g t) =
    expectedValue f + expectedValue g.
  Proof. by rewrite 3!expectedValue_expectedCondValue expectedCondValue_linear. Qed.

  Lemma expectedValue_const c : expectedValue (fun _ => c) = c.
  Proof.
    rewrite /expectedValue /expectedCondValue -mulr_suml.
    by case: (andP (dist_ax d)); move/eqP=> ->; rewrite mul1r.
  Qed.

  Lemma expectedValue_range f
        (H : forall x : T, 0 <= f x <= 1) :
    0 <= expectedValue f <= 1.
  Proof.      
    rewrite /expectedValue /expectedCondValue; apply/andP; split.
    apply: sumr_ge0=> i _; case H2: (f i == 0).
    { by move: (eqP H2)=> ->; rewrite mulr0. }
    { rewrite mulrC pmulr_rge0; first by apply: dist_positive.
      case: (andP (H i))=> H3 _.
      rewrite lt0r; apply/andP; split=> //.
      by apply/eqP=> H4; rewrite H4 eq_refl in H2. }
    rewrite -(@dist_normalized T rty d); apply: ler_sum.
    move=> i _; case H2: (d i == 0).
    { by move: (eqP H2)=> ->; rewrite mul0r. }
    rewrite mulrC ger_pmull; first by case: (andP (H i)).
    have H3: 0 <= d i by apply: dist_positive.
    rewrite ltr_def; apply/andP; split=> //.
    by apply/eqP=> H4; rewrite H4 eq_refl in H2.
  Qed.    

  Lemma expectedValue_nonneg f
        (H : forall x : T, 0 <= f x) :
    0 <= expectedValue f.
  Proof.      
    apply: sumr_ge0=> i _; case H2: (f i == 0).
    { by move: (eqP H2)=> ->; rewrite mulr0. }
    apply: mulr_ge0 => //; apply: dist_positive.
  Qed.    

  Lemma expectedCondValue_nonneg f (p : pred T)
        (H : forall x : T, 0 <= f x) :
    0 <= expectedCondValue f p.
  Proof.
    apply: divr_ge0.
    { apply: sumr_ge0=> i _; case H2: (f i == 0).
      { by move: (eqP H2)=> ->; rewrite mulr0. }
      apply: mulr_ge0 => //; apply: dist_positive. }
    apply: probOf_nonneg.
  Qed.      
End expectedValue.

Section cdf.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Fixpoint cdf_aux (x : T) (l : seq T) : rty :=
    if l is [:: y & l'] then
      if x == y then d y
      else d x + cdf_aux x l'
    else 0.

  Definition cdf (x : T) : rty := cdf_aux x (enum T).

  Fixpoint inverse_cdf_aux (p acc : rty) (cand : option T) (l : seq T)
    : option T :=
    if l is [:: y & l'] then
      if acc > p then cand
      else inverse_cdf_aux p (acc + d y) (Some y) l'
    else cand.

  Definition inverse_cdf (p : rty) : option T :=
    inverse_cdf_aux p 0 None (enum T).
End cdf.  

(** Product distributions *)

Lemma sum_ffunE'
      (aT : finType) (rty : numDomainType) (g : aT -> rty) :
  \sum_t [ffun x => g x] t =
  \sum_t g t.
Proof. by apply: eq_big=> // i _; rewrite ffunE. Qed.

Lemma prod_distr_sum
      (I J : finType) (rty : numDomainType) (F : I -> J -> rty) :
  \prod_i (\sum_j F i j) =
  \sum_(f : {ffun I -> J}) \prod_i F i (f i).
Proof. by apply: bigA_distr_bigA. Qed.

Section product.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable n : nat.
  Variable f : {ffun 'I_n -> dist T rty}.

  Notation type := ({ffun 'I_n -> T}).
  
  Definition prod_pmf : {ffun type -> rty} :=
    finfun (fun p : type => \prod_(i : 'I_n) f i (p i)).

  Lemma prod_pmf_dist :
    dist_axiom (T:=[finType of type]) (rty:=rty) prod_pmf.
  Proof.
    apply/andP; split.
    { rewrite /prod_pmf sum_ffunE'.
      rewrite -(@prod_distr_sum _ _ rty (fun x y => f x y)).
      have H: \prod_(i<n) (\sum_j (f i) j) = \prod_(i<n) 1.
      { apply: congr_big => // i _.
        by rewrite dist_normalized. }
      by rewrite H prodr_const expr1n. }
    apply/forallP => x; rewrite /prod_pmf ffunE.
    by apply: prodr_ge0 => i _; apply: dist_positive.
  Qed.    
  
  Definition prod_dist : dist [finType of type] rty :=
    @mkDist _ _ prod_pmf prod_pmf_dist.
End product.
  
Section uniform.
  Variable T : finType.
  Variable t0 : T.
  Notation rty := rat.
  
  Definition uniform_dist : {ffun T -> rty} :=
    finfun (fun _ => 1 / #|T|%:R).

  Lemma itern_addr_const n (r : rty) : iter n (+%R r) 0 = r *+ n.  
  Proof. by elim: n r=> // n IH r /=; rewrite IH mulrS. Qed.

  Lemma ffun_lem (r : rty) :
            \sum_(t : T) [ffun => r / #|T|%:R] t
          = \sum_(t : T) r / #|T|%:R.
  Proof. by apply/congr_big=> // i _; rewrite ffunE. Qed.
  
  Lemma uniform_normalized : dist_axiom uniform_dist.
  Proof.
    rewrite /dist_axiom ffun_lem; rewrite big_const itern_addr_const.
    have Hgt0: (#|T| > 0)%N.
    { move: (@enumP T); move/(_ t0)=> H; rewrite cardT.
      move: (mem_enum T t0); rewrite /in_mem /=.
        by case: (enum T).
    }
    have H: #|T| != 0%N.
    { by apply/eqP=> H; rewrite H in Hgt0.
    }
    apply/andP; split.    
    { move: #|T| H=> n.
      rewrite div1r -[_ *+ n]mulr_natl; move/eqP=> H.
      apply/eqP; apply: mulfV=> //; apply/eqP=> H2; apply: H.
      suff: n == 0%N; first by move/eqP=> ->.
      by erewrite <-pnatr_eq0; apply/eqP; apply: H2.
    }
    apply/forallP=> t; rewrite /uniform_dist ffunE.
    apply: divr_ge0=> //. 
    by apply: ler0n.
  Qed.

  Definition uniformDist : dist T [numDomainType of rat] := mkDist uniform_normalized.

  Lemma expectedValue_uniform (f : T -> rty) :
    expectedValue uniformDist f = (\sum_(t : T) (f t)) / #|T|%:R.
  Proof.
    rewrite /expectedValue /uniformDist /= /uniform_dist.
    rewrite mulr_suml; apply/congr_big=> // t _; rewrite ffunE.
    by rewrite -mulrA mul1r mulrC.
  Qed.      
End uniform.

(** Markov's Inequality *)

Section markov.
  Variable T : finType.
  Variable rty : numFieldType.
  Variable a : rty.
  Variable a_gt0 : 0 < a.
  Variable f : T -> rty.
  Variable f_nonneg : forall t, 0 <= f t.
  Variable d : dist T rty.

  Definition PRED := [pred x | f x >= a].
  
  Lemma markov : probOf d PRED <= expectedValue d f / a.
  Proof.
    rewrite /probOf; rewrite ->expectedValue_split with (p:=PRED).
    have H1: 0 <= \sum_(t | ~~ PRED t) d t * f t.
    { apply: sumr_ge0 => i H; apply: mulr_ge0 => //; apply: dist_positive. }
    rewrite ler_pdivl_mulr // mulrC.
    have H2:
      \sum_(t | PRED t) d t * f t
      <= \sum_(t | PRED t) d t * f t + \sum_(t | ~~ PRED t) d t * f t.
    { by rewrite ler_addl. }
    have H3: a * (\sum_(t | PRED t) d t) <= \sum_(t | PRED t) d t * f t.
    { rewrite mulr_sumr; apply: ler_sum => i; rewrite/PRED/= => Hi.
      rewrite mulrC ler_pmul => //; first by apply: dist_positive.
      by apply/ltrW. }
    apply: ler_trans; first by apply: H3.
    apply: H2.
  Qed.     
End markov.    
