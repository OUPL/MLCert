import numpy as np
import tensorflow as tf
from util import run_batches
import shared

def evaluate(sess, x, y, pred_op, images, labels, batch_size, log=False):
    preds = run_batches(sess, pred_op, [x], [images], batch_size)
    acc = np.sum(preds == labels) / len(labels)
    if log: print("accuracy: %0.04f" % acc)
    return acc

def compute_logits(sess, x, logits_op, images, batch_size):
    # images = images[:100]
    return run_batches(sess, logits_op, [x], [images], batch_size)

def compute_predictions(sess, x, preds_op, images, batch_size):
    # images = images[:100]
    return run_batches(sess, preds_op, [x], [images], batch_size)
