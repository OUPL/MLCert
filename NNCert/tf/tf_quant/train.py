import argparse, sys, time
import numpy as np
import tensorflow as tf
from batch_gen import batch_gen
from dataset_params import choose_dataset
from eval import evaluate

def init_session():
    gpu_options = tf.GPUOptions(per_process_gpu_memory_fraction=0.5)
    sess = tf.Session(config=tf.ConfigProto(gpu_options=gpu_options))
    return sess


# Train the model one minibatch at a time, occasionally printing the
# loss/accuracy on the training data and saving the best known weights
# at the time (best accuracy on the training data).
def train_model(model, x, y, loss_op, pred_op, weights,
                train_images, train_labels):
    train_op = model.training(loss_op, x, FLAGS.learning_rate,
                              FLAGS.decay_step, FLAGS.decay_factor)

    sess = init_session()
    tf.summary.scalar('loss', loss_op)
    summary_op = tf.summary.merge_all()
    summary_writer = tf.summary.FileWriter('logs', sess.graph)
    init = tf.global_variables_initializer()
    sess.run(init)
    minibatch_gen = batch_gen(FLAGS.batch_size, train_images.shape[0],
                              max_batches=FLAGS.max_steps, replace=True)

    highest_acc, best_weights = 0.0, model.get_weights(sess, weights)
    # i = 0

    print("training model...")

    start_time = time.time()
    for minibatch in minibatch_gen:
        batch_images, batch_labels = train_images[minibatch], \
                                     train_labels[minibatch]

        feed_dict = {x: batch_images, y: batch_labels }

        _, loss_values, summary = sess.run([train_op, loss_op, summary_op],
                                           feed_dict=feed_dict)
        summary_writer.add_summary(summary, minibatch_gen.counter)

        if minibatch_gen.counter % 1000 == 0:
            cur_time = time.time()
            duration = (cur_time - start_time)
            start_time = cur_time
            print('Step %d (%.3f sec): loss = ' %
                  (minibatch_gen.counter, duration) + str(loss_values))

        if minibatch_gen.counter % 1000 == 0:
            model.save_weights(sess, best_weights, FLAGS.model_dir,
                               num_bits=FLAGS.bits)
            acc = evaluate(sess, x, y, pred_op, train_images, train_labels,
                           FLAGS.batch_size)
            if acc >= highest_acc:
                highest_acc = acc
                best_weights = model.get_weights(sess, weights)
            if (acc >= FLAGS.stop):
                print("Reached stopping accuracy.")
                return
            
    evaluate(sess, x, y, pred_op, train_images, train_labels,
             FLAGS.batch_size)

    model.save_weights(sess, best_weights, FLAGS.model_dir,
                       num_bits=FLAGS.bits)
    print("highest accuracy: %f" % highest_acc)


def main(argv):
    # Load parameters and data for the chosen dataset.
    model, save_images, NUM_CLASSES, IMAGE_SIZE, example_shape, load_data \
        = choose_dataset(FLAGS.dataset +
                         ("" if FLAGS.pca == 0 else "_reduced"))
    train_data, validation_data, _ = load_data()

    # Combine train and validation sets for training.
    # images = np.concatenate([train_data.images, validation_data.images],
    #                         axis=0)
    # labels = np.concatenate([train_data.labels, validation_data.labels])

    # Trauin on only the training set.
    images, labels = train_data.images, train_data.labels

    with tf.Graph().as_default():

        # Build all of the ops.
        print("building computation graph...")
        x = tf.placeholder(tf.float32, example_shape(FLAGS.batch_size))
        y = tf.placeholder(tf.int32, shape=(FLAGS.batch_size))
        weights = model.weights(quantize=True, num_bits=FLAGS.bits, pca=FLAGS.pca)
        logits = model.inference(x, weights)
        loss_op = model.loss(logits, y)
        pred_op = model.predictions(logits)

        # Go.
        train_model(model, x, y, loss_op, pred_op, weights, images, labels)


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
        help='The factor by which to multiply the learning rate when it decays.'
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
        default=8,
        help='Number of bits for quantization.'
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
        help='0 to use original data, 1 for PCA transformed data.'
    )
    FLAGS, unparsed = parser.parse_known_args()
    tf.app.run(main=main, argv=[sys.argv[0]] + unparsed)
