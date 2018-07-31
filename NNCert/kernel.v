Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import List NArith ZArith ProofIrrelevance. Import ListNotations.
Require Import micromega.Lia.

Require Import OUVerT.dyadic OUVerT.numerics OUVerT.vector OUVerT.compile.

Require Import MLCert.axioms MLCert.bitvectors.

Require Import bitnet net.


Module Type TYPE.
  Parameter t : Type.
End TYPE.  

Module Type FINTYPE.
  Parameter t : finType.
End FINTYPE.

Module TypeOfFintype (T:FINTYPE) <: TYPE.
  Definition t:Type := T.t.
End TypeOfFintype.

(** We could use flattened vectors instead of matrices I guess but
    compilation and extraction seem to be a bit faster this way. *)
Module Type KernelType (IN N OUT : BOUND) (S T : TYPE).
  (* IN = dimensionality of the input space
     N = the number of hidden neurons
     S = the type of shift/scale parameters
     T = the type of network weights *)

  Definition Layer1Payload := AxVec IN.n T.t.
  Definition Layer1 := AxVec N.n Layer1Payload.

  Definition Layer2Payload := AxVec N.n T.t.
  Definition Layer2 := AxVec OUT.n Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1;
      layer2 : Layer2 }.
End KernelType.

Module Kernel (IN N OUT : BOUND) (S T : TYPE) <: KernelType IN N OUT S T.
  (* IN = dimensionality of the input space
      N = the number of hidden neurons
      S = the type of shift/scale parameters
      T = the type of network weights *)

  Definition Layer1Payload := AxVec IN.n T.t.
  Definition Layer1 := AxVec N.n Layer1Payload.

  Definition Layer2Payload := AxVec N.n T.t.
  Definition Layer2 := AxVec OUT.n Layer2Payload.

  Record t :=
    { ss1 : S.t * S.t;
      ss2 : S.t * S.t;
      layer1 : Layer1;
      layer2 : Layer2 }.
End Kernel.


(** A finType analog of KernelType:*)
Module Type KernelFinType (IN N OUT : BOUND) (S T : FINTYPE).
  Definition Layer1Payload := AxVec_finType IN.n T.t.
  Definition Layer1 := AxVec_finType N.n Layer1Payload.

  Definition Layer2Payload := AxVec_finType N.n T.t.
  Definition Layer2 := AxVec_finType OUT.n Layer2Payload.

  Definition t : finType :=
    [finType of ((S.t * S.t) * (S.t * S.t) * Layer1 * Layer2)].

  Definition ss1 (x:t) := let: (ss1, ss2, l1, l2) := x in ss1.
  Definition ss2 (x:t) := let: (ss1, ss2, l1, l2) := x in ss2.
  Definition l1 (x:t) := let: (ss1, ss2, l1, l2) := x in l1.
  Definition l2 (x:t) := let: (ss1, ss2, l1, l2) := x in l2.  
End KernelFinType.


Module KernelFin (IN N OUT : BOUND) (S T : FINTYPE) <: KernelFinType IN N OUT S T.
  Definition Layer1Payload := AxVec_finType IN.n T.t.
  Definition Layer1 := AxVec_finType N.n Layer1Payload.

  Definition Layer2Payload := AxVec_finType N.n T.t.
  Definition Layer2 := AxVec_finType OUT.n Layer2Payload.

  Definition t : finType :=
    [finType of ((S.t * S.t) * (S.t * S.t) * Layer1 * Layer2)].

  Definition ss1 (x:t) := let: (ss1, ss2, l1, l2) := x in ss1.
  Definition ss2 (x:t) := let: (ss1, ss2, l1, l2) := x in ss2.
  Definition l1 (x:t) := let: (ss1, ss2, l1, l2) := x in l1.
  Definition l2 (x:t) := let: (ss1, ss2, l1, l2) := x in l2.  
End KernelFin.


Module Type PayloadMap (T : TYPE).
  Parameter f : T.t -> DRed.t.
End PayloadMap.


Fixpoint range n :=
  match n with
  | O => nil
  | S n' => range n' ++ [n']
  end.


Module Translate (IN N OUT : BOUND) (S T : TYPE)
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
                                    (AxVec_to_list x))
                             (AxVec_to_list (K.layer1 k))) in

      let l2 := flatten (map (fun x : K.Layer2Payload =>
                                map (fun y : T.t =>
                                       DRed.add (DRed.mult scale2 (G.f y)) shift2)
                                    (AxVec_to_list x))
                             (AxVec_to_list (K.layer2 k))) in
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


(** Here's an instantiation of KernelType to an EMNIST network with 20 hidden 
    nodes, using 16-bit IEEE FP numbers as weights and shift/scale parameters. 

    We prove a cardinality lemma for the finType version of this kernel. *)

Import DyadicFloat16. (*for bits_to_bvec*)

Definition bitvec_to_bvec (n:nat) (v:bitvec n) : BitVec.t :=
  bits_to_bvec (bitvec_to_sparse_list v).

(** Cardinality proof for b=16, N=10*)

Module bitvec16Type <: TYPE.
  Definition t := bitvec 16.
End bitvec16Type.

Module bitvec16FinType <: FINTYPE.
  Definition t := bitvec_finType 16.
  Lemma card : #|t| = 2^16. Proof. by rewrite bitvec_card. Qed.
End bitvec16FinType.

Module bitvec16PayloadMap : PayloadMap bitvec16Type.
  Definition f (v:bitvec16Type.t) : DRed.t := to_dyadic (bitvec_to_bvec v).
End bitvec16PayloadMap.

Module IN_784 <: BOUND. Definition n := 784. Lemma n_gt0 : 0 < n. by []. Qed. End IN_784.
Module N_10 <: BOUND. Definition n := 10. Lemma n_gt0 : 0 < n. by []. Qed. End N_10.
Module OUT_10 <: BOUND. Definition n := 10. Lemma n_gt0 : 0 < n. by []. Qed. End OUT_10.

Module bitvec16_EMNIST_10_KernelType 
  : KernelType IN_784 N_10 OUT_10 bitvec16Type bitvec16Type
  := Kernel IN_784 N_10 OUT_10 bitvec16Type bitvec16Type.

Module bitvec16_EMNIST_10_KernelFinType 
  : KernelFinType IN_784 N_10 OUT_10 bitvec16FinType bitvec16FinType
  := KernelFin IN_784 N_10 OUT_10 bitvec16FinType bitvec16FinType.

Lemma card_bitvec16_EMNIST_10_KernelFinType :
  #|bitvec16_EMNIST_10_KernelFinType.t|
  = 2^(4*16 + 10*784*16 + 10*10*16). (*2^254144 causes stack overflow*)
Proof.
  rewrite /bitvec16_EMNIST_10_KernelFinType.t !card_prod bitvec16FinType.card.
  (*Layer 1*)
  rewrite /bitvec16_EMNIST_10_KernelFinType.Layer1.
  rewrite /bitvec16_EMNIST_10_KernelFinType.Layer1Payload.
  have H1: #|AxVec_finType IN_784.n bitvec16FinType.t| = 2^(784*16).
  { rewrite (@AxVec_card 784 16) => //.
    by rewrite bitvec_card. }
  rewrite (@AxVec_card 10 (784*16) _ H1).
  (*Layer 2*)
  rewrite /bitvec16_EMNIST_10_KernelFinType.Layer2.
  rewrite /bitvec16_EMNIST_10_KernelFinType.Layer2Payload.
  have H2: #|AxVec_finType N_10.n bitvec16FinType.t| = 2^(10*16).
  { rewrite (@AxVec_card 10 16 bitvec16FinType.t); first by reflexivity.
    rewrite bitvec_card; reflexivity. }
  rewrite (@AxVec_card 10 (10*16) _ H2).
  rewrite -!multE; rewrite <-!Nat.pow_add_r; rewrite !multE; reflexivity.
Qed.  

(** Cardinality proof for b=16, N=10*)

Module bitvec2Type <: TYPE.
  Definition t := bitvec 2.
End bitvec2Type.

Module bitvec2FinType <: FINTYPE.
  Definition t := bitvec_finType 2.
  Lemma card : #|t| = 2^2. Proof. by rewrite bitvec_card. Qed.
End bitvec2FinType.

Module bitvec2PayloadMap : PayloadMap bitvec2Type.
  Definition f (v:bitvec2Type.t) : DRed.t := to_dyadic (bitvec_to_bvec v).
End bitvec2PayloadMap.

Module bitvec2_EMNIST_10_KernelType 
  : KernelType IN_784 N_10 OUT_10 bitvec16Type bitvec2Type
  := Kernel IN_784 N_10 OUT_10 bitvec16Type bitvec2Type.

Module bitvec2_EMNIST_10_KernelFinType 
  : KernelFinType IN_784 N_10 OUT_10 bitvec16FinType bitvec2FinType
  := KernelFin IN_784 N_10 OUT_10 bitvec16FinType bitvec2FinType.

Lemma card_bitvec2_EMNIST_10_KernelFinType :
  #|bitvec2_EMNIST_10_KernelFinType.t|
  = 2^(4*16 + 10*784*2 + 10*10*2). 
Proof.
  rewrite /bitvec2_EMNIST_10_KernelFinType.t !card_prod bitvec16FinType.card.
  (*Layer 1*)
  rewrite /bitvec2_EMNIST_10_KernelFinType.Layer1.
  rewrite /bitvec2_EMNIST_10_KernelFinType.Layer1Payload.
  have H1: #|AxVec_finType IN_784.n bitvec2FinType.t| = 2^(784*2).
  { rewrite (@AxVec_card 784 2) => //.
    by rewrite bitvec_card. }
  rewrite (@AxVec_card 10 (784*2) _ H1).
  (*Layer 2*)
  rewrite /bitvec2_EMNIST_10_KernelFinType.Layer2.
  rewrite /bitvec2_EMNIST_10_KernelFinType.Layer2Payload.
  have H2: #|AxVec_finType N_10.n bitvec2FinType.t| = 2^(10*2).
  { rewrite (@AxVec_card 10 2 bitvec2FinType.t); first by reflexivity.
    rewrite bitvec_card; reflexivity. }
  rewrite (@AxVec_card 10 (10*2) _ H2).
  rewrite -!multE; rewrite <-!Nat.pow_add_r; rewrite !multE; reflexivity.
Qed.  

(*
Module b16 := TypeOfFintype bitvec16FinType.
Module b2 := TypeOfFintype bitvec2FinType.
Module KTranslate :=
  Translate IN_784 N_10 OUT_10 b16 b2 bitvec16PayloadMap bitvec2PayloadMap
            bitvec2_EMNIST_10_KernelType.
Import KTranslate. Import TheNet.
Import F. Import NETEval. Import NET.

Require Import Reals Fourier.
Require Import OUVerT.bigops OUVerT.dist OUVerT.chernoff OUVerT.learning.

Require Import MLCert.oracleclassifiers.

Definition X := NETEval.InputEnv.t.
Definition Y := Output.t.

Definition Params := bitvec2_EMNIST_10_KernelType.t.
*)

