# This file provides dataset-specific parameters and functions for
# MNIST and EMNIST.

import gzip, os, pickle
import tensorflow as tf
import numpy as np
from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet

def make_dataset(images, labels):
    return DataSet(images, labels, reshape=False, dtype=tf.uint8)


# MNIST

from tensorflow.examples.tutorials.mnist import input_data
from tensorflow.examples.tutorials.mnist import mnist
import mnist_model as mnist_model
from util import save_mnist_images as mnist_save_images

MNIST_NUM_CLASSES = 10
MNIST_IMAGE_SIZE = 28
PIXEL_DEPTH = 255

EMNIST_TRAIN_SAMPLES=200000
EMNIST_VALID_SAMPLES=40000
EMNIST_TEST_SAMPLES=40000

def mnist_example_shape(batch_size):
    return (batch_size, MNIST_IMAGE_SIZE * MNIST_IMAGE_SIZE)

def mnist_load_data():
    data_sets = input_data.read_data_sets('data')
    return data_sets.train, data_sets.validation, data_sets.test

# Code adapted from: https://gist.github.com/ischlag/41d15424e7989b936c1609b53edd1390
def extract_data(filename, num_images, start=0, IMAGE_SIZE=MNIST_IMAGE_SIZE):
    print('Extracting', filename)
    with gzip.open(filename) as bytestream:
        bytestream.read(16)
        bytestream.read(IMAGE_SIZE * IMAGE_SIZE * start)
        buf = bytestream.read(IMAGE_SIZE * IMAGE_SIZE * num_images)
        data = np.frombuffer(buf, dtype=np.uint8).astype(np.float32)
        scaled_data = np.array([x / PIXEL_DEPTH for x in data]).reshape(num_images, IMAGE_SIZE, IMAGE_SIZE)
        transposed_data = np.array([x.transpose().flatten() for x in scaled_data]) 
        return transposed_data

def extract_labels(filename, num_images, start=0):
    print('Extracting', filename)
    with gzip.open(filename) as bytestream:
        bytestream.read(8)
        bytestream.read(1 * start)
        buf = bytestream.read(1 * num_images)
        labels = np.frombuffer(buf, dtype=np.uint8).astype(np.int64)
        return labels
# END adapted code
    
def emnist_load_data():
    train_data = extract_data('emnist/emnist-digits-train-images-idx3-ubyte.gz', \
                              EMNIST_TRAIN_SAMPLES)
    train_labels = extract_labels('emnist/emnist-digits-train-labels-idx1-ubyte.gz', \
                                  EMNIST_TRAIN_SAMPLES)

    valid_data = extract_data('emnist/emnist-digits-train-images-idx3-ubyte.gz', \
                              EMNIST_VALID_SAMPLES, EMNIST_TRAIN_SAMPLES) #Validation at end of training set
    valid_labels = extract_labels('emnist/emnist-digits-train-labels-idx1-ubyte.gz', \
                                  EMNIST_VALID_SAMPLES, EMNIST_TRAIN_SAMPLES)

    test_data = extract_data('emnist/emnist-digits-test-images-idx3-ubyte.gz', \
                             EMNIST_TEST_SAMPLES)
    test_labels = extract_labels('emnist/emnist-digits-test-labels-idx1-ubyte.gz', \
                                 EMNIST_TEST_SAMPLES)

    train = make_dataset(train_data, train_labels)
    valid = make_dataset(valid_data, valid_labels)
    test = make_dataset(test_data, test_labels)
    return train, valid, test

def emnist_load_extracted_data():
    with open('emnist/train.pkl', 'rb') as f:
        train = pickle.load(f)
    with open('emnist/validation.pkl', 'rb') as f:
        validation = pickle.load(f)
    with open('emnist/test.pkl', 'rb') as f:
        test = pickle.load(f)
    return train, validation, test

# MNIST and EMNIST are available
def choose_dataset(set_name):
    if set_name.lower() == 'mnist':
        return mnist_model, mnist_save_images, MNIST_NUM_CLASSES, \
            MNIST_IMAGE_SIZE, mnist_example_shape, mnist_load_data
    elif set_name.lower() == 'emnist':
        # New data, but otherwise same as mnist
        return mnist_model, mnist_save_images, MNIST_NUM_CLASSES, \
            MNIST_IMAGE_SIZE, mnist_example_shape, emnist_load_extracted_data
            # MNIST_IMAGE_SIZE, mnist_example_shape, emnist_load_data
    else:
        return None
