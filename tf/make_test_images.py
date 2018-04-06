import gzip, pickle, os.path
import numpy as np
import tensorflow as tf
from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet
def make_dataset(images, labels):
    return DataSet(images, labels, reshape=False, dtype=tf.uint8)


# with open('emnist/train.pkl', 'rb') as f:
#     train = pickle.load(f, encoding='latin1')
# with open('emnist/validation.pkl', 'rb') as f:
#     validation = pickle.load(f, encoding='latin1')
with open('emnist/test.pkl', 'rb') as f:
    test = pickle.load(f, encoding='latin1')

with gzip.open('../test_images.pkl.gz', 'w') as f:
    pickle.dump(test.images, f)
