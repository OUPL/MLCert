import time
import numpy as np
import tensorflow as tf
from batch_gen import batch_gen
import shared
from eval import evaluate

# Train the model one minibatch at a time, occasionally printing the
# loss/accuracy on the training data and saving the best known weights
# at the time (best accuracy on the training data).

# This is now an iterator that returns the currently known best
# weights and accuracy of the current (not necessarily best) weights
# in a 2-tuple. The best weights and their correspondig accuracy are
# returned in the end.
def train_model(sess, model, x, y, train_op, loss_op, pred_op, weights,
                train_images, train_labels, batch_size, max_steps,
                model_dir, bits, stop, log=False):

    minibatch_gen = batch_gen(batch_size, train_images.shape[0],
                              max_batches=max_steps, replace=True)

    highest_acc, best_weights = 0.0, model.get_weights(sess, weights)

    if log: print("training model...")

    start_time = time.time()
    for minibatch in minibatch_gen:
        batch_images, batch_labels = train_images[minibatch], \
                                     train_labels[minibatch]

        feed_dict = { x: batch_images, y: batch_labels }

        _, loss_values = sess.run([train_op, loss_op], feed_dict=feed_dict)

        if minibatch_gen.counter % 1000 == 0:
            cur_time = time.time()
            duration = (cur_time - start_time)
            start_time = cur_time
            if log:
                print('Step %d (%.3f sec): loss = ' %
                      (minibatch_gen.counter, duration) + str(loss_values))

        if minibatch_gen.counter % 1000 == 0:
            model.save_weights(sess, best_weights, model_dir, num_bits=bits)
            acc = evaluate(sess, x, y, pred_op, train_images, train_labels,
                           batch_size)

            if acc >= highest_acc:
                highest_acc = acc
                best_weights = model.get_weights(sess, weights)

            if (acc >= stop):
                if log: print("Reached stopping accuracy.")
                return (best_weights, acc)
            else:
                yield (best_weights, acc)

    if log: print("highest accuracy: %f" % highest_acc)
    return (best_weights, highest_acc)
