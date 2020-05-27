#Python Implementation of the Budget Kernel Perceptron
import time
import numpy as np

#File IO to read in dataset
def format_line(line):
    if line == []:
        return []
    else:
        return [float(line[0])] + format_line(line[1:])
    
def format_label(y):
    if y == "True\n":
        return True 
    else:
        return False

def format_lines(lines):
    dataset = []
    datalabels = []
    for line in lines:
        y = line.split(',')
        dataset += [format_line(y[1:-1])]
        datalabels += [format_label(y[-1])]
    return (np.array(dataset), np.array(datalabels)) #dataset now stored as two numpy arrays

def setupEnv(trainfile, testfile):
    ftrain = open(trainfile, 'r')
    ftest = open(testfile, 'r')
    train, trainl = format_lines(ftrain.readlines())
    test, testl = format_lines(ftest.readlines())
    return (test, testl, train, trainl)

#Budget functions
def makeBudgetParams(n, sv):
    return [np.zeros(sv), np.zeros(n*sv).reshape(sv, n), np.repeat(False, sv)]

def linear_kernel(x, y):
    return np.dot(x, y)

def kernel_predict_budget(kernel, Params, example):
    d = Params[0]*linear_kernel(example,Params[1].T)
    d[np.logical_not(Params[2])] *= -1
    return np.sum(d) > 0.0

def existing(Params, j):
    return (j[0]==Params[1]).all(1).any()
    
def upd_weights(Params, j):
    for i in range(len(Params[0])):
        if np.equal(Params[1][i], j[0]).all():
            Params[0][i] += 1
            return Params

def add_new(Params, j):
    return[np.append(Params[0][1:], 1.0), np.vstack((Params[1][1:], np.array(j[0]))), np.append(Params[2][1:], j[1])]

def budget_update(Params, j):
    if existing(Params, j):
        return upd_weights(Params, j)
    else:
        return add_new(Params, j)
    
def print_generalization_err(kernel, test, testl, Params, train, trainl, m, mt):
    train_acc = 0
    test_acc = 0
    for example, label in zip(train, trainl):
        if label == kernel_predict_budget(kernel, Params, example):
            train_acc += 1
    
    for example, label in zip(test, testl):
        if label == kernel_predict_budget(kernel, Params, example):
            test_acc += 1
    
    train_acc /= m
    test_acc /= mt
    print("Training: ", train_acc)
    print("Test: ", test_acc)
    print("Generalization Error: ", abs(train_acc - test_acc))

def kperceptronbudget(n, sv, epochs, kernel, train, trainl, test, testl, m, mt):
    Params = makeBudgetParams(n, sv + 1)
    for i in range(epochs):
        for example, label in zip(train, trainl):
            predict = kernel_predict_budget(kernel, Params, example)
            if label != predict:
                Params = budget_update(Params, (example, label))
    print_generalization_err(kernel, test, testl, Params, train, trainl, m, mt)

#Timing
def trials(trainfile, testfile, n, m, sv, epochs, mt):
    print(trainfile)
    (test, testl, train, trainl) = setupEnv(trainfile, testfile)
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, trainl, test, testl, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, trainl, test, testl, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, trainl, test, testl, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, trainl, test, testl, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, trainl, test, testl, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    print("")

def main():
    trials("data/out1train.dat", "data/out1test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out2train.dat", "data/out2test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out3train.dat", "data/out3test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out4train.dat", "data/out4test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out5train.dat", "data/out5test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out6train.dat", "data/out6test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out7train.dat", "data/out7test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out8train.dat", "data/out8test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out9train.dat", "data/out9test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out10train.dat", "data/out10test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out11train.dat", "data/out11test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out12train.dat", "data/out12test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out13train.dat", "data/out13test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out14train.dat", "data/out14test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out15train.dat", "data/out15test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out16train.dat", "data/out16test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out17train.dat", "data/out17test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out18train.dat", "data/out18test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out19train.dat", "data/out19test.dat", 3, 1000, 100, 5, 1000)
    trials("data/out20train.dat", "data/out20test.dat", 3, 1000, 100, 5, 1000)
    
main()
