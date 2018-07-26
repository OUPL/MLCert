import gzip, pickle, os.path
import numpy as np

with gzip.open('models/default/mnist_params.pkl.gz', 'rb') as f:
    weights = pickle.load(f, encoding='latin1')

print(len(weights))

print(weights[0].shape)
# print(weights[1].shape)

# w0, w1 = weights
# for i in range(w0.shape[0]):
#     print(w0[i])
# for i in range(w1.shape[0]):
#     print(w1[i])

w0 = weights[0]
for i in range(w0.shape[0]):
    print(w0[i])
