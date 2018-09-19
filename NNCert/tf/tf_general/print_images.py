import gzip, pickle, os.path
import numpy as np

with gzip.open('small/test.pkl.gz', 'rb') as f:
    test = pickle.load(f, encoding='latin1')

images = test.images

print(len(images))

for i in range(10):
    print(images[i])
