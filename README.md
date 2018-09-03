# OUPL/MLCert

`OUPL/MLCert` is a collection of software tools and libraries for doing verified machine learning in the Coq proof assistant, where by "verified machine learning in Coq" we mean learning with certified generalization guarantees (e.g., bounds on expected accuracy of learned models). A technical report describing `OUPL/MLCert` is forthcoming. 

## BUILD

### Prerequisites

* Coq 8.8

We've tested in Coq 8.8.0. However, the software probably also builds in Coq 8.8.1.

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
