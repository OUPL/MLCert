Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Require Import List. Import ListNotations.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import OUVerT.chernoff OUVerT.learning OUVerT.bigops OUVerT.dist OUVerT.numerics OUVerT.dyadic.

Require Import MLCert.monads MLCert.samplers.

Section image_noise.
  Variables X Y : Type.
  Variables (T:Type) (T_min T_max : T).
  Variable example_mapM : forall M:Type->Type, (T -> M T) -> X -> M X.

  Context {training_set} `{Foldable training_set (X*Y)}.
  Context {sampler_state} `{BasicSamplers sampler_state}.  

  Variable r:Type.

  Definition NoiseM T := StateT (M:=@Cont r) sampler_state T.
  
  Section noise.
    Variable noise_index : T -> NoiseM T.
    
    Definition noise_example (xy:X*Y) : NoiseM (X*Y) := 
      let: (x,y) := xy in
      x' <-- example_mapM noise_index x;
      ret (ret (x',y)).

    Definition noise (t:training_set) : NoiseM training_set := 
      foldable_mapM noise_example t.
  End noise.
  
  (*A "salt-and-pepper" image noise model, with probability p corrupting index i to 
    either x_min or x_max (each with probability p*1/2)*)
  
  Definition salt_and_pepper_index (p:D) (t:T) : NoiseM T :=
    corrupt <-- bernoulli_sampler p;
    if corrupt then
      flip <-- bernoulli_sampler (Dmake 1 1);
      ret (if flip then T_min else T_max)
    else ret t.
  
  Definition salt_and_pepper (p:D) (t:training_set) : NoiseM training_set := 
    noise (salt_and_pepper_index p) t.

  (*A random-valued impulse noise model, with probability p corrupting index i to 
    a number in the range [0,255], chosen uniformly.*)
  
  Variable T_of_nat : nat -> T.
  
  Definition rv_impulse_index (p:D) (t:T) : NoiseM T := 
    corrupt <-- bernoulli_sampler p;
    if corrupt then
      i <-- uniform_sampler (m:=256);
      ret (T_of_nat i)
    else ret t.
  
  Definition rv_impulse (p:D) (t:training_set) : NoiseM training_set := 
    noise (rv_impulse_index p) t.
End image_noise.
