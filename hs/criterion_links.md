#Running Experimental Results using Criterion benchmarking

In order to evaluate the performance of the kernel perceptron family of algorithms on real and artificial datasets, there are several pieces of information that need to be captured: training error, testing error, generalization error, and timing data. So the Kernel Perceptron, Budget Kernel Perceptron, and Description Kernel Perceptron can be directly compared, the same training and testing sets should be used. My testing methodology has XX steps: creating data files containing training and testing data, developing Haskell drivers that can read from files and utilize Criterion benchmarking, and finally saving results to an Excel workbook.

#Data Sets

The three implementations will be tested against two real datasets (Iris and Mines vs. Rocks) as well as 20 generated data sets. 

The [Iris dataset](https://archive.ics.uci.edu/ml/datasets/iris) contains 150 samples in three classes. When two classes are grouped together, the dataset becomes linearly separable.

The [Mines vs. Rocks dataset](https://archive.ics.uci.edu/ml/datasets/Connectionist+Bench+%28Sonar,+Mines+vs.+Rocks%29) contains 208 samples in two classes, each with 60 attribues.

The 20 artificial data sets consist of samples with three attributes, each between -1.0 and 1.0.

#Reading from Files and Criterion Benchmarking

Using file i/o, the dataset files will be read into the Haskell driver programs. I will need to learn how file i/o works in Haskell but it doesn't look too bad.

I found several resources that will be helpful in integrating Criterion into the existing Haskell drivers. The documentation for [Criterion.Main](https://hackage.haskell.org/package/criterion-1.5.6.2/docs/Criterion-Main.html) lists the required functions and environment variables to run benchmarks. The [tutorial for Criterion](http://www.serpentine.com/criterion/tutorial.html) gives several examples with sample output. I also found an example in Criterion's repo that shows an [example with multiple environments](https://github.com/bos/criterion/blob/master/examples/Maps.hs). 

From these resources, I have designed the testing system in Haskell. For each of the real and artificial datasets, the files containing their training and testing data will be parsed and stored in Criterion environments, which allow variables to be passed into a benchmark. Using environments allows the benchmark to track the desired function without timing file i/o and converting datasets into the correct format. The main function in the driver program will list a series of benchmarks, each with its own environment. For each benchmark, an implementation of a kernel perceptron will be called, with some differences compared to the drivers that generate random data with each run. The sampler function does not need to generate the training data from a hyperplane and print the training set to the screen. Instead, the sampler will simply pass the training data into the rest of the machinery. The print_generalization_err function will also be simplified to only print the errors, not the entire model. With these changes, the benchmark should have minimal overhead for training and testing. For each data set, Criterion will run training and testing many times to evaluate the timing.

To run the testing systems, the Haskell executable should be run with the option --output and a filename with extension .html, as this option prints detailed statistical information, including graphs, into HTML. I plan to implement one testing file per implementation. If access to the lab computers is granted in future, each file can be run once to determine new timing results.

#Storing Results

Criterion benchmarking consists of timing analysis, which means that I will not be able to use Criterion to perform statistical analysis on the training, testing, and generalization error. To store my results, I plan to use an Excel workbook. Because my implementations are all deterministic and will generate the same model when run multiple times, I will record these results manually in the workbook. 



