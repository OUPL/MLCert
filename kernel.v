Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith ZArith ProofIrrelevance. Import ListNotations.
Require Import micromega.Lia.

Require Import OUVerT.dyadic OUVerT.numerics OUVerT.vector OUVerT.compile.
Require Import bitnet net.


(** We could use flattened vectors instead of matrices I guess but
    compilation and extraction seem to be a bit faster this way. *)
Module Type KernelType (IN N OUT : BOUND) (S T : PAYLOAD).
  (* IN = dimensionality of the input space
     N = the number of hidden neurons
     S = the type of shift/scale parameters
     T = the type of network weights *)

  Module Layer1Payload := MatrixPayload IN T.
  Module Layer1 := Vector N Layer1Payload.

  Module Layer2Payload := MatrixPayload N T.
  Module Layer2 := Vector OUT Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1.t;
      layer2 : Layer2.t }.
End KernelType.

Module Kernel (IN N OUT : BOUND) (S T : PAYLOAD) <: KernelType IN N OUT S T.
  (* IN = dimensionality of the input space *)
(*      N = the number of hidden neurons *)
(*      S = the type of shift/scale parameters *)
(*      T = the type of network weights *)

  Module Layer1Payload := MatrixPayload IN T.
  Module Layer1 := Vector N Layer1Payload.

  Module Layer2Payload := MatrixPayload N T.
  Module Layer2 := Vector OUT Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1.t;
      layer2 : Layer2.t }.
End Kernel.


Module Type PayloadMap (T : PAYLOAD).
  Parameter f : T.t -> DRed.t.
End PayloadMap.


Module KernelTranslate (IN N OUT : BOUND) (S T : PAYLOAD)
       (F : PayloadMap S) (G : PayloadMap T)
       (K : KernelType IN N OUT S T).

  (* Total number of parameters *)
  Module D.
    Definition n : nat := IN.n*N.n + N.n*OUT.n.
    Lemma n_gt0 : (0 < n)%nat.
      unfold n.
      generalize IN.n_gt0, N.n_gt0, OUT.n_gt0.
      move=> /leP H0 /leP H1 /leP H2; apply /leP.
      rewrite <- !plusE; rewrite <- !multE; nia.
    Qed.
  End D.

  Module TheNet := DyadicNet IN D OUT.
  Import TheNet. Import TheNet.F. Import NETEval.

  (** Translate a network kernel to a parameter environment. Assumes
      to_dense_list returns the list in ascending order by index. *)
  Definition translate : K.t -> ParamEnv.t :=
    fun k =>
      let shift1 := F.f (fst (K.ss1 k)) in
      let scale1 := F.f (snd (K.ss1 k)) in
      let shift2 := F.f (fst (K.ss2 k)) in
      let scale2 := F.f (snd (K.ss2 k)) in

      let l1 := flatten (map (fun p : K.Layer1.Ix.t * K.Layer1Payload.t =>
                                let (_, x) := p in
                                map (fun p : K.Layer1Payload.Vec.Ix.t * T.t =>
                                       let (_, y) := p in
                                       DRed.add (DRed.mult scale1 (G.f y)) shift1)
                                    (K.Layer1Payload.Vec.to_dense_list x))
                             (K.Layer1.to_dense_list (K.layer1 k))) in

      let l2 := flatten (map (fun p : K.Layer2.Ix.t * K.Layer2Payload.t =>
                                let (_, x) := p in
                                map (fun p : K.Layer2Payload.Vec.Ix.t * T.t =>
                                       let (_, y) := p in
                                       DRed.add (DRed.mult scale2 (G.f y)) shift2)
                                    (K.Layer2Payload.Vec.to_dense_list x))
                             (K.Layer2.to_dense_list (K.layer2 k))) in
      ParamEnv.of_list (zip (ParamEnv.Ix.enumerate_t) (rev (l1 ++ l2))).
End KernelTranslate.
