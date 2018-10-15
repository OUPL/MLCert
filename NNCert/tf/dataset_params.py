# This file provides dataset-specific parameters and functions for
# MNIST and EMNIST.

import gzip, os, pickle
import tensorflow as tf
import numpy as np
from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet
import shared


# MNIST

from tensorflow.examples.tutorials.mnist import input_data
from tensorflow.examples.tutorials.mnist import mnist
from util import save_mnist_images as mnist_save_images
from constants import *

# def mnist_example_shape(batch_size):
#     return (batch_size, MNIST_IMAGE_SIZE * MNIST_IMAGE_SIZE)

# def reduced_example_shape(batch_size, d):
#     return (batch_size, d**2)

def mnist_load_data(parent_dir=''):
    data_sets = input_data.read_data_sets(parent_dir + 'data')
    return data_sets.train, data_sets.validation, data_sets.test

def reduced_dataset(d):
    return None, MNIST_NUM_CLASSES, d, reduced_example_shape(d), \
        emnist_load_reduced_data

# MNIST and EMNIST are available
def choose_dataset(set_name):
    if set_name.lower() == 'mnist':
        return mnist_save_images, lambda x: mnist_load_data(x)
    elif set_name.lower() == 'emnist':
        # New data, but otherwise same as mnist
        return mnist_save_images, shared.emnist_load_extracted_data()
    elif set_name.lower() == 'emnist_pca':
        return None, shared.emnist_load_reduced_data
    else:
        return None
