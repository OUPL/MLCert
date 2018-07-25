Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith ZArith ProofIrrelevance. Import ListNotations.
Require Import micromega.Lia.

Require Import OUVerT.dyadic OUVerT.numerics OUVerT.vector OUVerT.compile.

Require Import MLCert.extraction MLCert.bitnet MLCert.net.


(** We could use flattened vectors instead of matrices I guess but
    compilation and extraction seem to be a bit faster this way. *)
Module Type KernelType (IN N OUT : BOUND) (S T : PAYLOAD).
  (* IN = dimensionality of the input space
     N = the number of hidden neurons
     S = the type of shift/scale parameters
     T = the type of network weights *)

  Definition Layer1Payload := HsListVec IN.n T.t.
  Definition Layer1 := HsListVec N.n Layer1Payload.

  Definition Layer2Payload := HsListVec N.n T.t.
  Definition Layer2 := HsListVec OUT.n Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1;
      layer2 : Layer2 }.
End KernelType.

Module Kernel (IN N OUT : BOUND) (S T : PAYLOAD) <: KernelType IN N OUT S T.
  (* IN = dimensionality of the input space
      N = the number of hidden neurons
      S = the type of shift/scale parameters
      T = the type of network weights *)

  Definition Layer1Payload := HsListVec IN.n T.t.
  Definition Layer1 := HsListVec N.n Layer1Payload.

  Definition Layer2Payload := HsListVec N.n T.t.
  Definition Layer2 := HsListVec OUT.n Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1;
      layer2 : Layer2 }.
End Kernel.


Module Type PayloadMap (T : PAYLOAD).
  Parameter f : T.t -> DRed.t.
End PayloadMap.


Fixpoint range n :=
  match n with
  | O => nil
  | S n' => range n' ++ [n']
  end.


Module Translate (IN N OUT : BOUND) (S T : PAYLOAD)
       (F : PayloadMap S) (G : PayloadMap T)
       (K : KernelType IN N OUT S T).

  (* Total number of parameters *)
  Module D.
    Definition n : nat := IN.n*N.n + N.n*OUT.n.
    Lemma n_gt0 : (0 < n)%nat.
      unfold n; generalize IN.n_gt0, N.n_gt0, OUT.n_gt0.
      move=> /leP H0 /leP H1 /leP H2; apply /leP.
      rewrite -!plusE -!multE; nia.
    Qed.
  End D.
  Module TheNet := DyadicNet IN D OUT.
  Import TheNet. Import TheNet.F. Import NETEval.

  (** Translate a network kernel to a parameter environment. Assumes
      to_dense_list returns the list in ascending order by index. *)
  Definition translate_kernel : K.t -> ParamEnv.t :=
    fun k =>
      let shift1 := F.f (fst (K.ss1 k)) in
      let scale1 := F.f (snd (K.ss1 k)) in
      let shift2 := F.f (fst (K.ss2 k)) in
      let scale2 := F.f (snd (K.ss2 k)) in

      let l1 := flatten (map (fun x : K.Layer1Payload =>
                                map (fun y : T.t =>
                                       DRed.add (DRed.mult scale1 (G.f y)) shift1)
                                    (HsListVec_to_list x))
                             (HsListVec_to_list (K.layer1 k))) in

      let l2 := flatten (map (fun x : K.Layer2Payload =>
                                map (fun y : T.t =>
                                       DRed.add (DRed.mult scale2 (G.f y)) shift2)
                                    (HsListVec_to_list x))
                             (HsListVec_to_list (K.layer2 k))) in
      ParamEnv.of_list (zip (ParamEnv.Ix.enumerate_t) (rev (l1 ++ l2))).

  Definition layer1Indices : list (list (nat*nat)) :=
    map (fun i => map (fun j => (i * IN.n + j, j)) (range IN.n)) (range N.n).
  Definition layer2Indices : list (list (nat*nat)) :=
    map (fun i => map (fun j => (IN.n * N.n + i * N.n + j, j)) (range N.n)) (range OUT.n).

  Definition genReLULayer
             (inputs : list t) (params : list param_var)
             (default_input : t) (default_param : param_var)
             (indices : list (list (nat*nat))) :=
    map (fun l => NReLU (NComb (map (fun p : nat*nat =>
                                    let (i, j) := p in
                                    (nth i params default_param,
                                     nth j inputs default_input))
                                 l))) indices.
  Definition genOutputLayer
             (inputs : list t) (params : list param_var)
             (default_input : t) (default_param : param_var)
             (indices : list (list (nat*nat))) :=
    map (fun l => NComb (map (fun p : nat*nat =>
                             let (i, j) := p in
                             (nth i params default_param,
                              nth j inputs default_input))
                          l)) indices.

  Definition weaken_list (n : nat) (l : list {x : nat | x < n})
    : list {x : nat | x < n.+1} :=
    map (fun x => exist _ (proj1_sig x) (ltnW (proj2_sig x))) l.

  Program Fixpoint bounded_range n : list {x : nat | x < n} :=
    match n with
    | O => nil
    | S n' => weaken_list (bounded_range n') ++ [n']
    end.

  Program Definition input_vars : list (NET.InputEnv.Ix.t) :=
    map (fun i => @NET.InputEnv.Ix.mk (N_of_nat (proj1_sig i)) _)
        (bounded_range IN.n).
  Next Obligation. by rewrite Nat2N.id. Qed.

  Program Definition param_vars :=
    map (fun i => @NET.ParamEnv.Ix.mk (N_of_nat (proj1_sig i)) _)
        (bounded_range ParamEnv.n).
  Next Obligation. by rewrite Nat2N.id. Qed.

  Definition default_input := NComb [].
  Program Definition default_param := @NET.ParamEnv.Ix.mk N0 _.
  Next Obligation. apply D.n_gt0. Qed.

  Definition neurons := genReLULayer (map NIn input_vars) param_vars
                                     default_input default_param
                                     layer1Indices.

  Definition outputs := genOutputLayer neurons param_vars
                                       default_input default_param
                                       layer2Indices.
End Translate.
