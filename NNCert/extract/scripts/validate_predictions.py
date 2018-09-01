import sys
import numpy as np

path = sys.argv[1]
n = int(sys.argv[2])
    
with open(path) as f:
    logits = np.array([[float(x) for x in f.readline().split()]
                       for _ in range(n)])
    labels = [int(x) for x in f.readline().split()]

    preds = np.argmax(logits, axis=1).tolist()

    good = all([x == y for x, y in zip(labels, preds)])

    print("Predictions valid: " + str(good))
