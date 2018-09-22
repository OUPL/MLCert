import argparse, sys, time
import numpy as np
import tensorflow as tf
from functools import reduce
from operator import mul
from dataset_params import choose_dataset
from train import train_model
from eval import evaluate
import float_model, quantized_model
from shared import build_ops, choose_images_labels, init_session

# This program can be used to either train or evaluate a model
# according to various options given by command line arguments.


def choose_model():
    return float_model if FLAGS.quantize == 0 else quantized_model

def main(argv):
    # Choose between float and quantized models.
    model = choose_model()

    if FLAGS.pca == 1 and FLAGS.dataset != 'emnist':
        print('Error: PCA only supported for EMNIST')
        exit(-1)

    # Load parameters and data for the chosen dataset.
    save_images, load_data = choose_dataset(
        FLAGS.dataset + ('' if FLAGS.pca == 0 else '_pca'))
    print ('loading data...')
    train_data, validation_data, test_data = load_data('')

    # Choose which set to use (train, test, etc.).
    images, labels = choose_images_labels(train_data, validation_data,
                                          test_data, FLAGS.set)
    example_shape = images.shape[1:]
    input_size = reduce(mul, example_shape, 1)

    with tf.Graph().as_default():

        # Build all of the ops.
        print("building computation graph...")
        x, y, weights, logits, loss_op, pred_op, train_op = build_ops(
            FLAGS.batch_size, FLAGS.bits, FLAGS.learning_rate,
            FLAGS.decay_step, FLAGS.decay_factor, model, input_size)

        # Create session and initialize variables.
        sess = init_session()

        # Go.
        i = 0
        if FLAGS.action.lower() == 'train':
            seq = train_model(sess, model, x, y, train_op, loss_op,
                              pred_op, weights, images, labels,
                              FLAGS.batch_size, FLAGS.max_steps,
                              FLAGS.model_dir, FLAGS.bits, FLAGS.stop,
                              log=False)
            for _, acc in seq:
                i += 1
                if i % 1000 == 0:
                    print('acc: %.02f' % acc)
        elif FLAGS.action.lower() == 'eval':
            model.load_weights(sess, FLAGS.model_dir, input_size,
                               num_bits=FLAGS.bits)
            acc = evaluate(sess, x, y, pred_op, images, labels,
                           FLAGS.batch_size, log=False)
            print('acc: %.02f' % acc)
        else:
            print('unknown action: ' + str(FLAGS.action))
            exit(-1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--learning_rate',
        type=float,
        default=0.1,
        help='Initial learning rate.'
    )
    parser.add_argument(
        '--decay_step', '-lds',
        type=int,
        default=100000,
        help='How many steps before decaying the learning rate.'
    )
    parser.add_argument(
        '--decay_factor', '-ldf',
        type=float,
        default=0.1,
        help='The factor by which to multiply the learning rate when it \
        decays.'
    )
    parser.add_argument(
        '--max_steps',
        type=int,
        default=20000,
        help='Number of training steps to run.'
    )
    parser.add_argument(
        '--batch_size',
        type=int,
        default=100,
        help='Batch size. Must divide evenly into the dataset sizes.'
    )
    parser.add_argument(
        '--model_dir',
        type=str,
        default='models/default',
        help='Directory to save the weights.'
    )
    parser.add_argument(
        '--dataset',
        type=str,
        default='mnist',
        help='MNIST, EMNIST, or EMNIST_reduced'
    )
    parser.add_argument(
        '--bits',
        type=int,
        default=32,
        help='Number of bits for weights.'
    )
    parser.add_argument(
        '--stop',
        type=float,
        default=1.0,
        help=''
    )
    parser.add_argument(
        '--pca',
        type=int,
        default=0,
        help='0 to use original data, 1 to use PCA data'
    )
    parser.add_argument(
        '--action',
        type=str,
        default='eval',
        help='\'train\' to train, \'eval\' to evaluate.'
    )
    parser.add_argument(
        '-s', '--set',
        type=int,
        default=2,
        help='0 to use test set, 1 for validation set, 2 for training \
        set, 3 for combined training and validation.'
    )
    parser.add_argument(
        '-q', '--quantize',
        type=int,
        default=0,
        help='0 for float weights, 1 for fixed-precision quantized weights'
    )
    
    FLAGS, unparsed = parser.parse_known_args()
    tf.app.run(main=main, argv=[sys.argv[0]] + unparsed)
