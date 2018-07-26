from math import sqrt
import numpy as np
from scipy.misc import imsave


# Assumes size of data is divisible by batch_size.
# Any remainder is not computed.
def run_batches(sess, op, vars, data, batch_size):
    i, acc = 0, []
    # Assume all elements in data have the same size as the first
    while i < data[0].shape[0]:
        next_i = i + batch_size
        batch_data = [x[i:next_i] for x in data]
        feed_dict = { k: v for (k, v) in zip(vars, batch_data) }
        acc.append(sess.run(op, feed_dict=feed_dict))
        i = next_i
    return np.concatenate(acc)


def save_mnist_images(images, dir, filename='all.jpg'):
    images = images - np.mean(images)
    images = images.reshape(images.shape[0], 28, 28)
    width = int(sqrt(images.shape[0]))
    overall_image = np.empty([0, 28 * width])
    current_row = np.empty([28, 0])
    i = 0
    for example in images:
        current_row = np.append(current_row, example, axis=1)
        i += 1
        if i >= width:
            overall_image = np.append(overall_image, current_row, axis=0)
            current_row = np.empty([28, 0])
            i = 0
    print('# of examples omitted from jpg: %d' % i)
    imsave(dir + '/' + filename, overall_image)


def save_cifar10_images(images, dir, filename='all.jpg'):
    width = int(sqrt(images.shape[0]))
    overall_image = np.empty([0, 32 * width, 3])
    current_row = np.empty([32, 0, 3])
    i = 0
    for example in images:
        current_row = np.append(current_row, example, axis=1)
        i += 1
        if i >= width:
            overall_image = np.append(overall_image, current_row, axis=0)
            current_row = np.empty([32, 0, 3])
            i = 0
    print('# of examples omitted from jpg: %d' % i)
    imsave(dir + '/' + filename, overall_image)
