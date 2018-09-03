# OUPL/MLCert

`OUPL/MLCert` is a collection of software tools and libraries for doing verified machine learning in the Coq proof assistant, where by "verified machine learning in Coq" we mean learning with certified generalization guarantees (e.g., bounds on expected accuracy of learned models). A technical report describing `OUPL/MLCert` is forthcoming. 

## BUILD

### Prerequisites

* Coq 8.8

* [OUPL/OUVerT](https://github.com/OUPL/OUVerT) 

The Ohio University Verification Toolkit, containing a number of lemmas used in MLCert.

### Build Instructions

* First build `OUPL/OUVerT`, by cloning the repository and following the instructions in [OUPL/OUVerT/README.md](https://github.com/OUPL/OUVerT/blob/master/README.md). Don't forget to do `make install` or `sudo make install`. 

* Then, in `OUPL/MLCert`, do:

```
make
make install
```

* To transfer neural networks trained in TensorFlow to Coq, follow the instructions in `OUPL/MLCert/NNCert`. 

## ORGANIZATION

Following are the primary directories and files used in the development:

* [NNCert/](https://github.com/OUPL/MLCert/tree/master/NNCert): Applies `OUPL/MLCert` to neural networks trained in TensorFlow
* [hs/](https://github.com/OUPL/MLCert/tree/master/hs): The directory in which Haskell programs are extracted (e.g., from `linearclassifiers.v`)
* [axioms.v](https://github.com/OUPL/MLCert/blob/master/axioms.v): Axioms used in the development
* [bitvectors.v](https://github.com/OUPL/MLCert/blob/master/bitvectors.v): Bitvectors implemented on top of the axiomatized arrays of `axioms.v`
* [extraction_hs.v](https://github.com/OUPL/MLCert/blob/master/extraction_hs.v): Haskell-specific extraction directives
* [extraction_ocaml.v](https://github.com/OUPL/MLCert/blob/master/extraction_ocaml.v): OCaml-specific extraction directives
* [float32.v](https://github.com/OUPL/MLCert/blob/master/float32.v): Axiomatized 32-bit floating point numbers, as used in `linearclassifiers.v`
* [monads.v](https://github.com/OUPL/MLCert/blob/master/monads.v): Defines the continuation monad used in `learners.v`
* [learners.v](https://github.com/OUPL/MLCert/blob/master/learners.v): Learners as probabilistic programs
* [linearclassifiers.v](https://github.com/OUPL/MLCert/blob/master/linearclassifiers.v): Specializes `learners.v` to linear classifiers and Perceptron

## EXAMPLES 

### Learners

MLCert defines supervised learners (file `learners.v`):
```
Module Learner.
  Record t (X Y Hypers Params : Type) :=
    mk { predict : Hypers -> Params -> X -> Y;
         update : Hypers -> X*Y -> Params -> Params }.
End Learner.
```
as pairs of 

* a `predict`ion function that, given hyperparameters `Hypers`, parameters `Params`, and an input `X`, produces a label `Y`; and
* and `update` function that maps hypers, `X*Y` pairs, and parameters to new parameters.

The following function:
```
  Definition learn_func (init:Params) (T:training_set) : Params := 
    foldrM (fun epoch p_epoch =>
      foldable_foldM (M:=Id) (fun xy p =>
        ret (Learner.update learner h xy p))
        p_epoch T)
      init (enum 'I_epochs).
```
defines a generic learning procedure that applies `update` to a training set `T` by folding `update` over `T` `epoch` times.

### Linear Threshold Classifiers 

Linear threshold classifiers (`linearclassifiers.v`) specialize the `predict` of generic learners to a linear prediction function of the form `ax + b > 0`. We implement such classifiers in MLCert as:

```
Section LinearThresholdClassifier.
  Variable n : nat. (*the dimensionality*)

  Definition A := float32_arr n. (*examples*)
  Definition B := bool. (*labels*)
  Definition Weights := float32_arr n.
  Definition Bias := float32.
  Definition Params := (Weights * Bias)%type.

  Section predict.
    Open Scope f32_scope.
    Definition predict (p : Params) (a : A) : B :=
      let: (w, b) := p in
      f32_dot w a + b > 0.
  End predict.
End LinearThresholdClassifier.
```
`n` is the dimensionality of the problem space. The type `A:=float32_arr n` defines size-`n` arrays of 32-bit floating-point numbers. A linear threshold classifier's parameters are pairs of `Weights` (also size-`n` floating-point numbers) and `Bias`es.

### Perceptron 

We further specialize `Learner` by adding to `predict` an `update` rule that implements the Perceptron algorithm, defined as:
```
  Definition update (h:Hypers) (example_label:A*B) (p:Params) : Params :=
    let: (example, label) := example_label in
    let: predicted_label := predict p example in
    if Bool.eqb predicted_label label then p
    else let: (w, b) := p in
    (f32_map2 (fun x1 x2 => x1 + (alpha h)*label*x2) w example, b+label).
```
We package Perceptron `update` with the generic prediction rule of linear threshold classifiers by constructing the following record: 
```
  Definition Learner : Learner.t A B Hypers Params :=
    Learner.mk
      (fun h => @predict n)
      update.
```

### Extraction Perceptron to Haskell

To extract the Perceptron `Learner` to Haskell, we build an "extractible" version of a probabilistic program that first samples a training set, then uses `learn_func` specialized to Perceptron to learn a linear classifier.
```
  Definition perceptron (r:Type) := 
    @extractible_main A B Params Perceptron.Hypers 
      (Perceptron.Learner n) hypers epochs _ (@list_Foldable (A*B)%type) r
    (fun T => ret T).
```
The function `perceptron` is parametric in the sampling procedure that produces training sets (to prove generalization results of Perceptron, we further specialize to a sampler that's assumed to produced `n` iid examples from a distribution `D`). 

To extract `perceptron` to Haskell, we do:
```
Extraction Language Haskell.
Extraction "hs/Perceptron.hs" perceptron.
```
These commands produce a new Haskell source file, `Perceptron.hs` in directory `MLCert/hs/`, that can be compiled and executed by doing: 
```
> cd hs/
> ghc PerceptronTest
> ./PerceptronTest
```
`PerceptronTest.hs` is an unverified shim program, written directly in Haskell, that constructs a random linearly separable data set on which to train the extracted `Perceptron.hs`, which it imports.

### From TensorFlow to Coq/MLCert

See directory [MLCert/NNCert/](https://github.com/OUPL/MLCert/tree/master/NNCert) for additional directions on compiling to MLCert models learned in external tools like TensorFlow.
