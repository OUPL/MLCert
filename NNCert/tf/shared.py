import gzip, pickle
import numpy as np
import tensorflow as tf
from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet

from constants import *
from util import load_pickled_files


def make_dataset(images, labels):
    return DataSet(images, labels, reshape=False, dtype=tf.uint8)

def init_session():
    gpu_options = tf.GPUOptions(per_process_gpu_memory_fraction=0.5)
    sess = tf.Session(config=tf.ConfigProto(gpu_options=gpu_options))
    init = tf.global_variables_initializer()
    sess.run(init)
    return sess

# def init_placeholders(batch_size, example_shape):
#     x = tf.placeholder(tf.float32, example_shape)
#     y = tf.placeholder(tf.int32, shape=(batch_size))
#     return x, y

def emnist_load_data(parent_dir=''):
    train_data = extract_data(
        parent_dir + '/emnist/emnist-digits-train-images-idx3-ubyte.gz', \
        EMNIST_TRAIN_SAMPLES)
    train_labels = extract_labels(
        parent_dir + '/emnist/emnist-digits-train-labels-idx1-ubyte.gz', \
        EMNIST_TRAIN_SAMPLES)

    #Validation at end of training set
    valid_data = extract_data(
        parent_dir + '/emnist/emnist-digits-train-images-idx3-ubyte.gz', \
        EMNIST_VALID_SAMPLES, EMNIST_TRAIN_SAMPLES)
    valid_labels = extract_labels(
        parent_dir + '/emnist/emnist-digits-train-labels-idx1-ubyte.gz', \
        EMNIST_VALID_SAMPLES, EMNIST_TRAIN_SAMPLES)

    test_data = extract_data(
        parent_dir + '/emnist/emnist-digits-test-images-idx3-ubyte.gz', \
        EMNIST_TEST_SAMPLES)
    test_labels = extract_labels(
        parent_dir + '/emnist/emnist-digits-test-labels-idx1-ubyte.gz', \
        EMNIST_TEST_SAMPLES)

    return tuple([make_dataset(data, labels) for data, labels in
                  zip([train_data, valid_data, test_data],
                      [train_labels, valid_labels, test_labels])])

def emnist_load_extracted_data(postfix=''):
    return lambda prefix : \
        load_pickled_files([prefix + 'emnist/train' + postfix + '.pkl',
                            prefix + 'emnist/validation' + postfix + '.pkl',
                            prefix + 'emnist/test' + postfix + '.pkl'])

def emnist_load_reduced_data(prefix):
    return emnist_load_extracted_data('_pca')(prefix)

# Code adapted from:
# https://gist.github.com/ischlag/41d15424e7989b936c1609b53edd1390
def extract_data(filename, num_images, start=0, IMAGE_SIZE=MNIST_IMAGE_SIZE):
    print('Extracting', filename)
    with gzip.open(filename) as bytestream:
        bytestream.read(16)
        bytestream.read(IMAGE_SIZE * IMAGE_SIZE * start)
        buf = bytestream.read(IMAGE_SIZE * IMAGE_SIZE * num_images)
        data = np.frombuffer(buf, dtype=np.uint8).astype(np.float32)
        scaled_data = np.array([x / PIXEL_DEPTH for x in data]).reshape(
            num_images, IMAGE_SIZE, IMAGE_SIZE)
        transposed_data = np.array([x.transpose().flatten()
                                    for x in scaled_data]) 
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

def choose_images_labels(train, valid, test, i):
    images = test.images if i == 0 else \
             valid.images if i == 1 else \
             train.images if i == 2 else \
             np.concatenate([train.images, valid.images], axis=0)
    labels = test.labels if i == 0 else \
             valid.labels if i == 1 else \
             train.labels if i == 2 else \
             np.concatenate([train.labels, valid.labels], axis=0)
    return images, labels

def build_ops(batch_size, bits, learning_rate, decay_step,
              decay_factor, model, input_size, hidden_sizes):
    if bits == 16: dtype = tf.float16
    elif bits == 32: dtype = tf.float32
    else:
        # print('shared.build_ops warning: unexpected value %d for \
        # bits, defaulting to 32' % bits)
        dtype = tf.float32

    x = tf.placeholder(dtype, (batch_size, input_size))
    y = tf.placeholder(tf.int32, shape=batch_size)
    weights = model.weights(input_size, hidden_sizes, num_bits=bits)
    logits = model.inference(x, weights, len(hidden_sizes))
    loss_op = model.loss(logits, y)
    pred_op = model.predictions(logits)
    train_op = model.training(loss_op, x, learning_rate, decay_step,
                              decay_factor)
    return x, y, weights, logits, loss_op, pred_op, train_op
