Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Extraction.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist OUVerT.dyadic OUVerT.numerics.

Require Import MLCert.monads.

Class BasicSamplers (T : Type) : Type := 
  mkBasicSamplers {
      init_sampler_state : T;

      bernoulli_sampler : forall (r:Type) (p:D), StateT (M:=@Cont r) T bool;
      bernoulli_sampler_ok : 
        forall (s:T) (p:D) (f:bool -> R),
          bernoulli_sampler p s (fun bs' => let: (b,s') := bs' in f b) =
          big_sum (enum bool_finType) (fun b => Bernoulli.t (Rdefinitions.Q2R (D_to_Q p)) b * f b)%R;

      uniform_sampler : forall (r:Type) (m:nat), StateT (M:=@Cont r) T 'I_m;
      uniform_sampler_ok :
        forall (s:T) (m:nat) (f:'I_m -> R),
          @uniform_sampler _ m s (fun rs' => let: (r,s') := rs' in f r) = 
          big_sum (enum 'I_m) (fun x => (1 / mR m) * f x)%R
    }.
      
