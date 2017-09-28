Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import compile.

Definition map_split {aT bT : Type} (m : M.t (aT*bT)) :=
    M.fold (fun i r acc =>
              match r with
              | (a, b) =>
                (M.add i a acc.1, M.add i b acc.2)
              end)
           m (M.empty aT, M.empty bT).

Lemma map_split_spec (aT bT : Type) i (a : aT) (b : bT) m :
  M.find i m = Some (a, b) ->
  M.find i (map_split m).1 = Some a /\
  M.find i (map_split m).2 = Some b.
Proof.
  { rewrite /map_split. apply MProps.fold_rec_weak.
    { move => mo m' a' H0 H1 H2.
      have H3: (forall (k : M.key) (e : (aT*bT)),
                   M.MapsTo k e mo <-> M.MapsTo k e m').
      { by apply MProps.F.Equal_mapsto_iff; apply H0. }
      apply M.find_2 in H2. apply H3 in H2. apply M.find_1 in H2.
      apply H1. apply H2. }
    { move => H. inversion H. }
    { move => k e a' m' H0 IH. case: e. move => a0 b0 H2 /=.
      rewrite MProps.F.add_o. case: (MProps.F.eq_dec k i) => H3 //.
      rewrite MProps.F.add_eq_o in H2; auto. inversion H2.
      split. auto. rewrite MProps.F.add_eq_o //.
      split. apply IH. rewrite MProps.F.add_neq_o in H2.
      apply H2. apply H3.
      rewrite MProps.F.add_neq_o. apply IH.
      rewrite MProps.F.add_neq_o in H2.
      apply H2. apply H3. apply H3. } }
Qed.
