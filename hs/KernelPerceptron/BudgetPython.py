#Python Implementation of the Budget Kernel Perceptron, Naive version
#See KernelPerceptronBudgetPython.md for documentation
import time

#File IO to read in dataset not timed
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
    for line in lines:
        y = line.split(',')
        dataset += [(format_line(y[1:-1]), format_label(y[-1]))]
    return dataset

def setupEnv(trainfile, testfile):
    ftrain = open(trainfile, 'r')
    ftest = open(testfile, 'r')
    train = format_lines(ftrain.readlines())
    test = format_lines(ftest.readlines())
    return (test, train)

#Budget functions
def init_weights(n):
    weights = []
    for i in range(n):
        weights += [0.0]
    return weights

def makeBudgetParams(n, sv):
    Params = []
    for i in range(sv):
        Params += [(0.0, (init_weights(n), False))]
    return Params

def linear_kernel(x, y):
    dot = 0.0
    for xi, yi in zip(x, y):
        dot += xi * yi
    return dot

def float_of_bool(y):
    if y:
        return 1.0
    else:
        return -1.0

def kernel_predict_budget(kernel, Params, example):
    ret = 0.0
    for i in Params:
        ret += float_of_bool(i[1][1]) * i[0] * kernel(example, i[1][0])
    return (ret > 0.0)

def existing(Params, j):
    xj = j[0]
    for i in Params:
        if xj == i[1][0]:
            return True
    return False
    
def upd_weights(Params, j):
    for i in range(len(Params)):
        if Params[i][1][0] == j[0]:
            new_index = Params[i][0] + 1
            Params[i] = (new_index, j)
            return Params

def add_new(Params, j):
    #return ([(1.0, j)] + Params[:-1])
    return (Params[1:] + [(1.0, j)])

def budget_update(Params, j):
    if existing(Params, j):
        return upd_weights(Params, j)
    else:
        return add_new(Params, j)
    
def print_generalization_err(kernel, test, Params, train, m, mt):
    train_acc = 0
    test_acc = 0
    for i in train:
        example = i[0]
        label = i[1]
        if label == kernel_predict_budget(kernel, Params, example):
            train_acc += 1
    
    for i in test:
        example = i[0]
        label = i[1]
        if label == kernel_predict_budget(kernel, Params, example):
            test_acc += 1
    
    train_acc /= m
    test_acc /= mt
    print("Training: ", train_acc)
    print("Test: ", test_acc)
    print("Generalization Error: ", abs(train_acc - test_acc))

def kperceptronbudget(n, sv, epochs, kernel, train, test, m, mt):
    Params = makeBudgetParams(n, sv + 1)
    for i in range(epochs):
        for j in train:
            example = j[0]
            label = j[1]
            if label != kernel_predict_budget(kernel, Params, example):
                Params = budget_update(Params, j)
    print_generalization_err(kernel, test, Params, train, m, mt)

#Timing
def trials(trainfile, testfile, n, m, sv, epochs, mt):
    print(trainfile)
    (test, train) = setupEnv(trainfile, testfile)
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, test, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, test, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, test, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, test, m, mt)
    end = time.time()
    print("Training and Testing Time: %1.3f"% (end - start))
    start = time.time()
    kperceptronbudget(n, sv, epochs, linear_kernel, train, test, m, mt)
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
