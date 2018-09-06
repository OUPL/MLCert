import gzip, pickle, sys
import numpy as np

path1 = sys.argv[1]
path2 = sys.argv[2]

xs = []
ys = []

with open(path1) as f:
    xs = [[float(x) for x in line.split()] for line in f]

with open(path2) as f:
    ys = [[float(x) for x in line.split()] for line in f]

xs = xs[2:]

threshold = 0.001

def g(l):
    l1, l2 = l
    return [abs(x - y) for x, y in zip(l1, l2)]

i = 0
for l in list(map(g, zip(xs, ys))):
    for x in l:
        if x > threshold:
            print('the %dth weight differs by %f' % (i, x))
    i += 1

print('Done validating kernel.')
