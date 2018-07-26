import argparse, sys, pickle
import numpy as np
import tensorflow as tf
from dataset_params import choose_dataset
from util import run_batches, save_mnist_images

FLAGS = None


def init_placeholders(batch_size, example_shape):
    x = tf.placeholder(tf.float32, example_shape)
    y = tf.placeholder(tf.int32, shape=(batch_size))
    return x, y


def init_session():
    gpu_options = tf.GPUOptions(per_process_gpu_memory_fraction=0.5)
    sess = tf.Session(config=tf.ConfigProto(gpu_options=gpu_options))
    init = tf.global_variables_initializer()
    sess.run(init)
    return sess


def evaluate(sess, x, y, pred_op, images, labels, batch_size):
    preds = run_batches(sess, pred_op, [x], [images], batch_size)
    acc = np.sum(preds == labels) / len(labels)
    print("accuracy: %0.04f" % acc)
    return acc

def compute_logits(sess, x, logits_op, images, batch_size):
    images = images[:100]
    logits = run_batches(sess, logits_op, [x], [images], batch_size)
    for l in logits:
        print(l)

def compute_predictions(sess, x, preds_op, images, batch_size):
    images = images[:100]
    preds = run_batches(sess, preds_op, [x], [images], batch_size)
    print(preds)

def main(argv):
    model, save_images, NUM_CLASSES, IMAGE_SIZE, example_shape, load_data \
        = choose_dataset(FLAGS.dataset)
    train_data, validation_data, test_data = load_data()
    images = test_data.images if FLAGS.set == 0 else \
             validation_data.images if FLAGS.set == 1 else \
             train_data.images if FLAGS.set == 2 else \
             np.concatenate([train_data.images, validation_data.images],
                            axis=0)
    labels = test_data.labels if FLAGS.set == 0 else \
             validation_data.labels if FLAGS.set == 1 else \
             train_data.labels if FLAGS.set == 2 else \
             np.concatenate([train_data.labels, validation_data.labels],
                            axis=0)

    with tf.Graph().as_default():
        print("building computation graph...")
        x, y = init_placeholders(FLAGS.batch_size,
                                 example_shape(FLAGS.batch_size))
        weights = model.weights(quantize=True, num_bits=FLAGS.bits)
        logits = model.inference(x, weights)
        pred_op = model.predictions(logits)
        sess = init_session()
        model.load_weights(sess, FLAGS.model_dir, num_bits=FLAGS.bits)

        evaluate(sess, x, y, pred_op, images, labels, FLAGS.batch_size)
        # compute_logits(sess, x, logits, images, FLAGS.batch_size)
        # compute_predictions(sess, x, pred_op, images, FLAGS.batch_size)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--batch_size',
        type=int,
        default=100,
        help='Batch size.  Must divide evenly into the dataset sizes.'
    )
    parser.add_argument(
        '--input_data_dir',
        type=str,
        default='../../mnist/data',
        help='Directory to put the input data.'
    )
    parser.add_argument(
        '--model_dir',
        type=str,
        default='models/default',
        help='Directory to load the weights from.'
    )
    parser.add_argument(
        '-s', '--set',
        type=int,
        default=0,
        help='0 to evaluate on test set, 1 for validation set, 2 for training set, 3 for combined training and validation.'
    )
    parser.add_argument(
        '--dataset',
        type=str,
        default='mnist',
        help='MNIST or EMNIST'
    )
    parser.add_argument(
        '--bits',
        type=int,
        default=8,
        help='Number of bits for quantization.'
    )
    FLAGS, unparsed = parser.parse_known_args()
    tf.app.run(main=main, argv=[sys.argv[0]] + unparsed)
