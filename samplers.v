Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist OUVerT.dyadic OUVerT.numerics.

Require Import MLCert.monads MLCert.learners MLCert.float32.

Axiom sampler_state : Type.
Axiom init_sampler_state : sampler_state.

Axiom bernoulli_sampler : forall p:D, State sampler_state bool.
Axiom bernoulli_sampler_ok : 
  forall (s:sampler_state) (p:D) (f:bool -> R),
    let: (b,s') := bernoulli_sampler p s in 
    f b = big_sum (enum bool_finType) (fun b => Bernoulli.t (Qreals.Q2R (D_to_Q p)) b * f b).

Axiom uniform_sampler : forall m:nat, State sampler_state 'I_m.
Axiom uniform_sampler_ok :
  forall (s:sampler_state) (m:nat) (f:'I_m -> R),
    let: (r,s') := uniform_sampler m s in 
    f r = big_sum (enum 'I_m) (fun x => (1 / mR m) * f x).

