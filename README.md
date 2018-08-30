# OUPL/MLCert

`OUPL/MLCert` is a collection of software tools and libraries for doing verified machine learning in the Coq proof assistant, where by "verified machine learning in Coq" we mean learning with certified generalization guarantees (e.g., bounds on expected accuracy of learned models).

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
