Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.dist.

Local Open Scope ring_scope.

Section importance.
  Variable T: finType.
  Variable rty: realFieldType.
  Variables f g: dist T rty.
  Variable fg_support: support f =i support g.
  Variable X: T -> rty.

  Lemma importance:
    expectedValue f X = expectedValue g (fun x => f(x)/g(x) * X x).
  Proof.
    rewrite /expectedValue; apply: eq_big => // i _.
    rewrite mulrA [_ / _]mulrC mulrA.
    case H: (i \in support f).
    { move: fg_support => /(_ i); rewrite H => H2.
      rewrite divff; first by rewrite mul1r.
      by apply/eqP => H3; rewrite in_set H3 ltrr in H2. }
    have: (i \in support g) = false by rewrite -fg_support H.
    move => H2; rewrite in_set in H; rewrite in_set in H2.
    have H3: f i = 0.
    { by move: (dist_positive f i); rewrite ler_eqVlt H orbC /=; move/eqP. }
    have H4: g i = 0.
    { by move: (dist_positive g i); rewrite ler_eqVlt H2 orbC /=; move/eqP. }
    by rewrite H3 H4 !mulr0.
  Qed.
End importance.