import numpy as np
import tensorflow as tf
from dataset_params import emnist_load_data
import pickle

from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet

def make_dataset(images, labels):
    return DataSet(images, labels, reshape=False, dtype=tf.uint8)

train, validation, test = emnist_load_data()

with open("emnist/train.pkl", "wb") as f:
    pickle.dump(train, f)

with open("emnist/validation.pkl", "wb") as f:
    pickle.dump(validation, f)

with open("emnist/test.pkl", "wb") as f:
    pickle.dump(test, f)

# all = make_dataset(np.concatenate([train.images,
#                                    validation.images,
#                                    test.images],
#                                   axis=0),
#                    np.concatenate([train.labels, 
#                                    validation.labels,
#                                    test.labels]))


# with open("emnist/all.pkl", "wb") as f:
#     pickle.dump(all, f)
