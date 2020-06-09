# KernelPerceptronDrivers.md

This file provides documentation for the Haskell driver files for the Kernel Perceptron and its variants produced by running `make` in the root of MLCert.

## Table of Contents

- [Summary of Haskell Extraction Process](#summary-of-haskell-extraction-process)
- [Directory structure](#directory-structure)
- [File Naming Conventions](#file-naming-conventions)
- [Types of Haskell Driver Files](#types-of-haskell-driver-files)
 - [XOR: Kernel Perceptron](#xor-kernel-perceptron)
 - [Test: Randomly Generated Dataset Drivers](#test-randomly-generated-dataset-drivers)
 - [RunFile: Input Dataset Drivers](#runfile-input-dataset-drivers)
 - [FileIO: Timing Analysis Drivers](#fileio-timing-analysis-drivers)
- [Required Haskell Libraries](#required-haskell-libraries)
- [Real and Synthetic Dataset Specifications](#real-and-synthetic-dataset-specifications)
- [Compilation and Execution](#compilation-and-execution)

## Summary of Haskell Extraction Process

In order for the Coq implementations to be run, the implementations must be extracted to a Haskell module. The extracted Haskell implementations do not contain a main or code to generate or read dataset files. Therefore, unverified driver files in Haskell are necessary to run the implementations on real inputs.

Each Haskell driver has a similar structure with four main features: global variables, parameter initialization, dataset generation or file I/O, and the main definition. First, the driver defines several global parameters such as the dimensionality of the data, the number of training examples, and any other hyperparameters that may be necessary. These global variables are often used in functions that create and initialize the parameters for the algorithm before training. The drivers all include functions to either generate training and testing sets randomly or load a dataset in from a file. All these definitions are used in the main function, which executes the Kernel Perceptron variant.

The `hs/KernelPerceptron/` directory contains Haskell drivers, dataset files, and documentation of experiments.

## Directory structure

The files and directories in MLCert pertinent to the Kernel Perceptron are as follows:

```bash
MLCert
├── hs
│   ├── KernelPerceptron
│   │   ├── data
│   │   ├── timing_drivers
│   │   │   ├── timing_outputs
│   │   │   └── <FileIO Drivers>
│   │   ├── KP_Performance_Results.xlsx
│   │   └── <Test and RunFile Drivers>
└── kernelperceptron.v
```

In the `MLCert/` directory, the Kernel Perceptron implementations in Coq are defined in `kernelperceptron.v`, which extracts the Coq implementations to two locations: `MLCert/hs/KernelPerceptron/` and `MLCert/hs/KernelPerceptron/timing_drivers/`. These locations correspond to the two locations of Haskell driver files, as denoted in the above diagram. 

The dataset files for the Kernel Perceptron are found in `MLCert/hs/KernelPerceptron/data/`. The datasets have been preprocessed to match the file I/O code in some of the driver files. Each dataset consists of a training file and a testing file. The naming conventions and formatting of the datasets are described in [File Naming Conventions](#file-naming-conventions) and [Real and Synthetic Dataset Specifications](#real-and-synthetic-dataset-specifications), respectively.

Documentation of the results of performance tests can be found in the `KP_Performance_Results.xlsx` spreadsheet in `MLCert/hs/KernelPerceptron` and the `MLCert/hs/KernelPerceptron/timing_drivers/timing_outputs` directory, which contains the scripted output of the drivers recording the runtime of training and testing.

## File Naming Conventions

Driver and data file names follow specific conventions. The file name for driver files contains two main pieces of information: the implementation executed and the kind of dataset or training procedure. 

There are three variants of the Kernel Perceptron algorithm implemented in MLCert: the Kernel Perceptron, Budget Kernel Perceptron, and Description Kernel Perceptron. Driver files for the Kernel Perceptron begin with `KPerceptron`. The Budget Kernel Perceptron's files start with `KPerceptronBudget`. `KPerceptronDes` is the beginning of the Description Kernel Perceptron's drivers.

There are four different kinds of training procedures: `XOR`, `Test`, `RunFile`, and `FileIO`. These form the end of the file name, and are each detailed in [Types of Haskell Driver Files](#types-of-haskell-driver-files).

The data file naming conventions for the real and synthetic datasets denote the type of dataset and whether the specific file is a training set file or a test set file. There are three kinds of datasets in `MLCert/hs/KernelPerceptron/data/`: synthetic, iris, and sonar. For all three types of datasets, the file names end in either `train` or `test` to separate the training set from the test set.

The synthetic dataset files all begin with `out` followed by the index of the synthetic dataset from 1-20. 

The iris dataset files begin with `iris` and two datasets were created based on a roughly 50/50 split between training and test examples and a 75/25 split. `iris50train.dat` matches with `iris50test.dat`, and `iris75train.dat` is paired with `iris25test.dat`. 

Like the iris dataset, the sonar dataset files were also used to create two datasets, one with a 50/50 split and another with a 75/25 split. The sonar dataset files all begin with `sonar`. In addition to the original sonar dataset files, there are also normalized dataset files that in the range [-1, 1] instead of [0, 1]. The normalized files have `norm` in their file names.

## Types of Haskell Driver Files

The four training/testing procedures are outlined in the sections below. The `XOR`, `Test`, and `RunFile` drivers are all found in `MLCert/hs/KernelPerceptron/`. The `FileIO` drivers are found in `MLCert/hs/KernelPerceptron/timing_drivers/`.

### XOR: Kernel Perceptron 

The driver `KPerceptronXOR.hs` verifies that the quadratic kernel for the Kernel Perceptron perfectly classifies the XOR function as the classic example of a nonlinear dataset. The four data points of the XOR function are hardcoded as both the training and test sets. Because this is a test of the quadratic kernel, this driver is only implemented for the Kernel Perceptron. This is the only file with nonlinear data.

### Test: Randomly Generated Dataset Drivers

The `Test` drivers such as `KPerceptronBudgetTest.hs` generate a new random linearly-separable dataset each time the program is run. To generate the training and test sets, the program first randomly generates a list of `n` float32 values between -1 and 1, which denotes the `n`-dimensional linear hyperplane which will be used to label the training and test examples. Each training and test example is compared to the hyperplane to generate its label, producing linearly separable training and test sets. 

These drivers ensure that the implementations can be run, but are not terribly useful for comparing two implementations, since the datasets are different with each execution.

### RunFile: Input Dataset Drivers

The `RunFile` drivers run a specific dataset as opposed to generating a new dataset randomly. The input dataset is divided into two files, one for the training set and one for the test set. Each line of the data files must be formatted as follows:

`36,5.1,3.5,1.4,0.2,True`

The first value of the line must be an integer, counting down to 0 on the last line. This is the unique index value used in the Kernel Perceptron and thrown away by the Budget and Description Kernel Perceptrons. Following the unique index, the `n` data values are separated by commas. The last value of the line is either `True` or `False`, which corresponds to the label of the example. The driver contains functions that read each line, split the lines on the commas, and format the data into the appropriate data types such as Ordinal, float32, and Bool. 

This driver runs one specific dataset without any timing analysis. 

### FileIO: Timing Analysis Drivers

The `FileIO` drivers run one or more datasets and output the runtime for training and testing each dataset. There are a total of 3 `FileIO` drivers, 1 for each implementation. To run just one trial or dataset, one or more of the calls to `trials` can be commented out. The `FileIO` driver functions are modified from the `RunFile` drivers to remove all global variables for the dimensionality of the data and size of the dataset so multiple datasets can be read and timed in one execution of the script.

File input is the same as for the `RunFile` drivers.

Training and testing are run 5 times to record the runtime. Reading the dataset files is not included in the timing analysis.

## Required Haskell Libraries

Several Haskell Libraries are imported by the driver programs:

```
System.Random (Test)
System.IO (RunFile and FileIO)
Data.List.Split (RunFile and FileIO)
Data.Bool (RunFile and FileIO)
System.CPUTime (FileIO)
Text.Printf (FileIO)
```

These should be included in the standard installation of Haskell.

## Real and Synthetic Dataset Specifications

This section describes how each of the real and synthetic datasets were generated or sourced, as well as preprocessing and normalization.

Synthetic: Using the output of 20 runs of `KPerceptronTest.hs`, 20 synthetic datasets were created. The 20 artificial data sets were defined by different linear hyperplanes and consist of samples with three attributes, each between -1.0 and 1.0. Because these datasets were created by the Kernel Perceptron, their datafiles just had to be modified from the command line output. Unique indices were already present. 

Iris: The [Iris dataset](https://archive.ics.uci.edu/ml/datasets/iris) contains 150 samples in three classes. When two classes are grouped together, the dataset becomes linearly separable. However, this dataset is not divided into a training set vs testing set, which is necessary for calculating generalization error. To create training and testing files, I used a Python script to divide samples at random between the training and testing set based on a specified ratio, such as 50/50 for one iris dataset and 75/25 for another iris dataset. Two different splits were chosen because more training examples can improve accuracy. After the four iris training and testing files were created, I manually added the unique identifiers to the beginning of each line and changed the labels from `Iris-XXXX` to Boolean.

Sonar: The [Mines vs. Rocks dataset](https://archive.ics.uci.edu/ml/datasets/Connectionist+Bench+%28Sonar,+Mines+vs.+Rocks%29) contains 208 samples in two classes, each with 60 attribues. Like the iris dataset, I used a Python script to create a 50/50 split for one sonar dataset and 75/25 for another. In addition to adding the unique identifiers and changing the labels from `M` or `R` to Boolean, I also created normalized data files that change each value from between [0,1] to [-1,1]. This normalization improves the performance for the Kernel Perceptron because this dataset takes many epochs to converge.

## Compilation and Execution

To compile these Haskell drivers, I use `ghc driver.hs` and execute with `./driver`. No command line arguments are necessary for either compilation or execution.
