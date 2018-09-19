import gzip, pickle, os.path
import tensorflow as tf
from tensorflow.contrib.quantize.python import quant_ops
from quantize import quantize_ndarray, dequantize_ndarray

from constants import MNIST_NUM_CLASSES as NUM_CLASSES
from constants import MNIST_IMAGE_SIZE as IMAGE_SIZE

IMAGE_PIXELS = IMAGE_SIZE**2
NUM_HIDDEN_LAYERS = 1
HIDDEN_SIZES = [10] # length should equal NUM_HIDDEN_LAYERS
WEIGHT_DECAY = 0.00002


def weights(name='mnist', reuse=None, num_bits=8, pca_d=0):
    image_pixels = IMAGE_PIXELS if pca_d == 0 else pca_d**2
    with tf.variable_scope(name, reuse=reuse):
        sizes = HIDDEN_SIZES + [NUM_CLASSES]
        w0 = tf.get_variable(
            'w0',
            (image_pixels, sizes[0]),
            initializer=tf.contrib.layers.xavier_initializer())
        ws = [w0] + [tf.get_variable(
            'w' + str(i+1), [sizes[i], sizes[i+1]],
            initializer=tf.contrib.layers.xavier_initializer())
                     for i in range(NUM_HIDDEN_LAYERS)]
        weight_decay = tf.multiply(sum([tf.nn.l2_loss(w) for w in ws]),
                                   WEIGHT_DECAY, name='weight_loss')
        tf.add_to_collection('losses', weight_decay)
        ws = [quant_ops.MovingAvgQuantize(w, num_bits=num_bits) for w in ws]
        return ws

def inference(images, weights, name='mnist', reuse=None):
    with tf.variable_scope(name, reuse=reuse):
        l = images
        for i in range(NUM_HIDDEN_LAYERS):
            l = tf.nn.relu(tf.matmul(l, weights[i]))
        out = tf.matmul(l, weights[-1])
        return out


# The loss op. Take average cross-entropy loss over all of the
# examples in the batch and add the weight decay term.
def loss(logits, y):
    labels = tf.cast(y, tf.int64)
    cross_entropy = tf.nn.sparse_softmax_cross_entropy_with_logits(
        labels=labels, logits=logits, name='cross_entropy_per_example')
    cross_entropy_mean = tf.reduce_mean(cross_entropy)

    # This is just the single weight decay term in this case
    weight_reg = tf.add_n(tf.get_collection('losses'))

    # The loss is defined as the cross entropy loss plus the weight
    # decay term (L2 loss).
    loss = cross_entropy_mean + weight_reg

    return loss


# The training op.
def training(loss, x, learning_rate, decay_step, decay_factor):
    global_step = tf.Variable(0, name='global_step', trainable=False)
    lr = tf.train.exponential_decay(learning_rate, global_step, decay_step,
                                    decay_factor, staircase=True)
    optimizer = tf.train.GradientDescentOptimizer(lr)
    grads = optimizer.compute_gradients(loss)
    train_op = optimizer.apply_gradients(grads)
    return train_op


# Run the network forward to produce predicted labels.
def predictions(logits):
    return tf.cast(tf.argmax(logits, axis=1), tf.int32)


def test_weights(sess, quantized_weights, num_bits=8):
    ws = sess.run(quantized_weights, feed_dict = {})
    print(ws[0][0])

    bounds = [x.eval(sess) for x in
              filter(lambda x: 'min:0' in x.name or 'max:0' in x.name,
                     tf.get_collection(tf.GraphKeys.GLOBAL_VARIABLES))]

    quantized = [quantize_ndarray(ws[0], bounds[0], bounds[1],
                                  num_bits=num_bits),
                 quantize_ndarray(ws[1], bounds[2], bounds[3],
                                  num_bits=num_bits)]
    all_vars = quantized + bounds

    weights2 = all_vars[:-4]
    bounds2 = all_vars[-4:]
    w0 = dequantize_ndarray(weights2[0], bounds2[0], bounds2[1],
                            num_bits=num_bits)
    w1 = dequantize_ndarray(weights2[1], bounds2[2], bounds2[3],
                            num_bits=num_bits)
    print(w0[0])

def save_weights(sess, weights, dir='models', num_bits=8):
    os.makedirs(dir, exist_ok=True)
    bounds = [x.eval(sess) for x in
              filter(lambda x: 'min:0' in x.name or 'max:0' in x.name,
                     tf.get_collection(tf.GraphKeys.GLOBAL_VARIABLES))]

    quantized = [quantize_ndarray(weights[0], bounds[0], bounds[1],
                                  num_bits=num_bits),
                 quantize_ndarray(weights[1], bounds[2], bounds[3],
                                  num_bits=num_bits)]

    all_vars = quantized + bounds
    with gzip.open(dir + "/params.pkl.gz", "w") as f:
        pickle.dump(tuple(all_vars), f)

def print_weights(sess, weights, num_bits=8):
    bounds = [x.eval(sess) for x in
              filter(lambda x: 'min:0' in x.name or 'max:0' in x.name,
                     tf.get_collection(tf.GraphKeys.GLOBAL_VARIABLES))]

    quantized = [quantize_ndarray(weights[0], bounds[0], bounds[1],
                                  num_bits=num_bits),
                 quantize_ndarray(weights[1], bounds[2], bounds[3],
                                  num_bits=num_bits)]

    print(quantized)

def get_weights(sess, weights_op):
    return sess.run(weights_op, feed_dict = {})

def load_weights(sess, dir, model_name='mnist', num_bits=8, pca_d=0):
    image_pixels = IMAGE_PIXELS if pca_d == 0 else pca_d**2
    filename = dir + '/params.pkl.gz' if dir else 'params.pkl.gz'
    with gzip.open(filename, 'rb') as f:
        vars = pickle.load(f, encoding='latin1')
        weights = vars[:-4]
        bounds = vars[-4:]

        # print(vars[1])
        # print(len(vars))

        w0 = dequantize_ndarray(weights[0], bounds[0], bounds[1],
                                num_bits=num_bits)
        w1 = dequantize_ndarray(weights[1], bounds[2], bounds[3],
                                num_bits=num_bits)
        
        # for w in w0.flatten(order='F'):
        #     print(w)
        # for w in w1.flatten(order='F'):
        #     print(w)
        
        with tf.variable_scope(model_name, reuse=True):
            sizes = [image_pixels] + HIDDEN_SIZES + [NUM_CLASSES]
            w0_var = tf.get_variable('w0', [sizes[0], sizes[1]])
            w1_var = tf.get_variable('w1', [sizes[1], sizes[2]])
            sess.run([w0_var.assign(w0)])
            sess.run([w1_var.assign(w1)])
            min0 = tf.get_variable('MovingAvgQuantize/min')
            max0 = tf.get_variable('MovingAvgQuantize/max')
            min1 = tf.get_variable('MovingAvgQuantize_1/min')
            max1 = tf.get_variable('MovingAvgQuantize_1/max')
            sess.run([min0.assign(bounds[0]), max0.assign(bounds[1]),
                      min1.assign(bounds[2]), max1.assign(bounds[3])])
