import argparse, sys, time
import numpy as np
import tensorflow as tf
from dataset_params import choose_dataset
from train import train_model
from eval import evaluate
import float_model, quantized_model
from shared import init_session


def choose_model():
    return float_model if FLAGS.quantize == 0 else quantized_model


def main(argv):
    model = choose_model()

    # Load parameters and data for the chosen dataset.
    save_images, NUM_CLASSES, IMAGE_SIZE, example_shape, load_data \
        = choose_dataset(FLAGS.dataset +
                         ("" if FLAGS.pca_d == 0 else "_reduced"))
    print ('loading data...')
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

        # Build all of the ops.
        print("building computation graph...")
        x = tf.placeholder(tf.float32, example_shape(FLAGS.batch_size))
        y = tf.placeholder(tf.int32, shape=(FLAGS.batch_size))
        weights = model.weights(num_bits=FLAGS.bits, pca_d=FLAGS.pca_d)
        logits = model.inference(x, weights)
        loss_op = model.loss(logits, y)
        pred_op = model.predictions(logits)
        train_op = model.training(loss_op, x, FLAGS.learning_rate,
                                  FLAGS.decay_step, FLAGS.decay_factor)
        sess = init_session()

        # Go.
        if FLAGS.action.lower() == 'train':
            seq = train_model(sess, model, x, y, train_op, loss_op,
                              pred_op, weights, images, labels,
                              FLAGS.batch_size, FLAGS.max_steps,
                              FLAGS.model_dir, FLAGS.bits, FLAGS.stop,
                              log=False)
            for _, acc in seq:
                print('acc: %.02f' % acc)
        elif FLAGS.action.lower() == 'eval':
            model.load_weights(sess, FLAGS.model_dir, num_bits=FLAGS.bits,
                               pca_d=FLAGS.pca_d)
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
        '--pca_d',
        type=int,
        default=0,
        help='0 to use original data, otherwise the value provided \
        determines the number of principal components in PCA transform \
        (n = pca_d²).'
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
