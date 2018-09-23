import gzip, pickle, os.path
import tensorflow as tf

from constants import MNIST_NUM_CLASSES as NUM_CLASSES

INCLUDE_BIASES = False
WEIGHT_DECAY = 0.00002


def weights(input_size, hidden_sizes, name='mnist', reuse=None, num_bits=32):
    if num_bits == 16: dtype = tf.float16
    elif num_bits == 32: dtype = tf.float32
    else:
        print('float_model.weights warning: unexpected value %d for \
        num_bits, defaulting to 32' % num_bits)
        dtype = tf.float32

    with tf.variable_scope(name, reuse=reuse):
        sizes = hidden_sizes + [NUM_CLASSES]
        w0 = tf.get_variable(
            'w0',
            (input_size, sizes[0]),
            initializer=tf.contrib.layers.xavier_initializer(),
            dtype=dtype)
        ws = [w0] + [tf.get_variable(
            'w' + str(i+1), [sizes[i], sizes[i+1]],
            initializer=tf.contrib.layers.xavier_initializer(),
            dtype=dtype) for i in range(len(hidden_sizes))]
        weight_decay = tf.multiply(sum([tf.nn.l2_loss(w) for w in ws]),
                                   WEIGHT_DECAY, name='weight_loss')
        tf.add_to_collection('losses', weight_decay)
        return ws

# This builds the feedforward network op and returns it. A weight
# decay term is added to a collection so it can be referred to by the
# loss function.
def inference(images, weights, num_hidden, name='m0', reuse=None):
    with tf.variable_scope(name, reuse=reuse):
        l = images
        for i in range(num_hidden):
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


# def get_weights(sess):
#     return tuple(map(lambda x: x.eval(sess),
#                      tf.trainable_variables()))
def get_weights(sess, weights_op):
    return sess.run(weights_op, feed_dict = {})

# num_bits is ignored.
def save_weights(sess, weights, dir='models', num_bits=0):
    os.makedirs(dir, exist_ok=True)
    with gzip.open(dir + "/params.pkl.gz", "w") as f:
        pickle.dump(weights, f)


def load_weights(sess, dir, input_size, hidden_sizes,
                 model_name='mnist', num_bits=32):
    if num_bits == 16: dtype = tf.float16
    elif num_bits == 32: dtype = tf.float32
    else:
        print('float_model.load_weights warning: unexpected value %d for \
        num_bits, defaulting to 32' % num_bits)
        dtype = tf.float32
    filename = dir + '/params.pkl.gz' if dir else 'params.pkl.gz'
    with gzip.open(filename, 'rb') as f:
        weights = pickle.load(f, encoding='latin1')

        # for w in weights[0].flatten(order='F'):
        #     print(w)
        # for w in weights[1].flatten(order='F'):
        #     print(w)

        with tf.variable_scope(model_name, reuse=True):
            sizes = [input_size] + hidden_sizes + [NUM_CLASSES]
            for i in range(NUM_HIDDEN_LAYERS+1):
                w_var = tf.get_variable('w' + str(i),
                                        [sizes[i], sizes[i+1]],
                                        dtype=dtype)
                sess.run([w_var.assign(weights[i])])
