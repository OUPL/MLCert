# KernelPerceptronBudgetPython.md

This file provides documentation for the two Python implementations of the Budget Kernel Perceptron.

## Table of Contents

- [Reasoning for a Budget Kernel Perceptron in Python](#reasoning-for-a-budget-kernel-perceptron-in-python)
- [Differences between Python Implementations](#differences-between-python-implementations)
- [Required Python Libraries](#required-python-libraries)
- [Input Dataset Specifications](#Input-dataset-specifications)
- [Execution](#execution)

## Reasoning for a Budget Kernel Perceptron in Python

The Haskell implementations, extracted from Coq, are the primary implementations used to examine the generalization error and runtime of the Kernel Perceptron variants. However, Haskell is not often used for machine learning applications. Python is one of the primary languages used for machine learning at present due to libraries such as Numpy and Scipy that have made scientific computing more efficient and accessible for students and researchers. The Budget Kernel Perceptron was implemented in Python so that its generalization error and runtime performance could be compared to the Haskell implementation.

## Differences between Python Implementations

The `hs/KernelPerceptron/` directory contains the Python implementations as well as the dataset files. The file `BudgetPython.py` implements the Budget Kernel Perceptron with functions and data structures that directly correspond to the Haskell functions and data structures, a naive way of translating Haskell to Python. The file `BudgetPythonNumpy.py`, however, uses the Numpy library of arrays and functions in its implementation, making the Numpy implementation much closer to real-world machine learning. 

The naive Budget Kernel Perceptron is structured the same as the Haskell implementation with a few differences. The Haskell implementation uses 32-bit floating point numbers, but the naive Python uses the built-in `float` type, which is 64-bit. The naive Python functions that iterate through the parameters or the training and testing sets using for loops instead of recursive folding. In the Haskell implementation, there are several global variables that are used by many of the functions implicitly. In Python, no global variables are used to make it possible to run dataset files with different sizes. These differences simplify the Budget Kernel Perceptron implmentation.

The Numpy Budget Kernel Perceptron makes many changes to the naive Python functions. Because Numpy is most efficient when Numpy functions and data structures are used, some of the types were modified to be more compatible, such as the type of Params. In Haskell and naive Python, the type of Params is a list of tuples, where a float value is paired with a support vector, whose type is a float array paired with a Boolean label. Instead of this [(float, (float_array, bool))] type, in Numpy, the list of tuples is changed to a tuple of three arrays, an array of the parameters for each support vector, an array of support vectors, and an array of labels. This change to the parameter types makes vectorization much easier and aids in the use of Numpy functions. The Numpy changes do not impact the result of the calculations, but Numpy optimizes calculations and when done correctly, speeds up computation.

## Required Python Libraries

To time the Python training and testing, the time library is used by both Python implementations. The Numpy Python implementation requires the Numpy library. No other libraries are necessary.

## Input Dataset Specifications

The Python implementations do not time the file input of reading in the datasets before training, matching the Haskell implementation. The same dataset files can be read in by the Python implementations as Haskell. The dataset files must conform to the following format. The input dataset is divided into two files, one for the training set and one for the test set. Each line of the data files must be formatted as follows:

`36,5.1,3.5,1.4,0.2,True`

The first value of the line must be an integer, counting down to 0 on the last line. This value is thrown away by the Budget Kernel Perceptron, but is necessary for the Kernel Perceptron. Following the unique index, `n` data values are separated by commas, where `n` is the dimensionality of the input data. The last value of the line is either `True` or `False`, which corresponds to the label of the example. The driver contains functions that read each line, split the lines on the commas, and format the data into the appropriate data types such as `float` and `Boolean`. 

## Execution

To run the Python implementations, no command line arguments are necessary. To run `BudgetPython.py`:

`python3 BudgetPython.py`

To run `BudgetPythonNumpy.py`:

`python3 BudgetPythonNumpy.py`
