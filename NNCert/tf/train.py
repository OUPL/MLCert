import argparse, sys, time
import numpy as np
import tensorflow as tf
from batch_gen import batch_gen
from dataset_params import choose_dataset
from eval import evaluate

FLAGS = None

# set using the function below from the flags parameter
DTYPE, NP_DTYPE = None, None

def set_dtype():
    global DTYPE, NP_DTYPE
    if FLAGS.bits == '32':
        DTYPE = tf.float32
        NP_DTYPE = np.float32
    elif FLAGS.bits == '16':
        DTYPE = tf.float16
        NP_DTYPE = np.float16
    else:
        print('bits must be 16 or 32')
        sys.exit(1)


def init_session():
    gpu_options = tf.GPUOptions(per_process_gpu_memory_fraction=0.5)
    sess = tf.Session(config=tf.ConfigProto(gpu_options=gpu_options))
    return sess


# Train the model one minibatch at a time, occasionally printing the
# loss/accuracy on the training data and saving the weights.
def train_model(model, x, y, loss_op, pred_op, train_images, train_labels):
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

    print("training model...")

    start_time = time.time()
    for minibatch in minibatch_gen:
        batch_images, batch_labels = train_images[minibatch], \
                                     train_labels[minibatch]

        feed_dict = {x: batch_images, y: batch_labels}
        # feed_dict = {x: batch_images.astype(NP_DTYPE), y: batch_labels}

        _, loss_values, summary = sess.run([train_op, loss_op, summary_op],
                                           feed_dict=feed_dict)
        summary_writer.add_summary(summary, minibatch_gen.counter)

        if minibatch_gen.counter % 1000 == 0:
            cur_time = time.time()
            duration = (cur_time - start_time)
            start_time = cur_time
            print('Step %d (%.3f sec): loss = ' %
                  (minibatch_gen.counter, duration) + str(loss_values))

        if minibatch_gen.counter % 10000 == 0:
            model.save_weights(sess, FLAGS.model_dir)
            evaluate(sess, x, y, pred_op, train_images, train_labels,
                     FLAGS.batch_size)

    model.save_weights(sess, FLAGS.model_dir)


def main(argv):
    # Load parameters and data for the chosen dataset.
    model, save_images, NUM_CLASSES, IMAGE_SIZE, example_shape, load_data \
        = choose_dataset(FLAGS.dataset)
    train_data, _, _ = load_data()
    set_dtype()

    with tf.Graph().as_default():

        # Build all the ops
        print("building computation graph...")
        x = tf.placeholder(DTYPE, example_shape(FLAGS.batch_size))
        y = tf.placeholder(tf.int32, shape=(FLAGS.batch_size))
        logits = model.inference(x, dtype=DTYPE)
        loss_op = model.loss(logits, y)
        pred_op = model.predictions(logits)

        # Go
        train_model(model, x, y, loss_op, pred_op,
                    train_data.images.astype(NP_DTYPE), train_data.labels)


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
        default=10000,
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
        help='MNIST or EMNIST'
    )
    parser.add_argument(
        '--bits',
        type=str,
        default='32',
        help='MNIST or EMNIST'
    )
    FLAGS, unparsed = parser.parse_known_args()
    tf.app.run(main=main, argv=[sys.argv[0]] + unparsed)
