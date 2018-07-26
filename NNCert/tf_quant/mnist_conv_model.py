import gzip, pickle, os.path
import tensorflow as tf

NUM_CLASSES = 10
IMAGE_SIZE = 28
IMAGE_PIXELS = IMAGE_SIZE * IMAGE_SIZE
WEIGHT_DECAY = 0.00002

FC_SIZE_1 = 384
FC_SIZE_2 = 192


def _variable_on_cpu(name, shape, initializer):
  dtype = tf.float32
  var = tf.get_variable(name, shape, initializer=initializer, dtype=dtype)
  return var

def _variable_with_weight_decay(name, shape, stddev, wd):
  dtype = tf.float32
  var = tf.get_variable(
      name, shape,
      initializer=tf.truncated_normal_initializer(stddev=stddev, dtype=dtype),
      dtype=dtype)
  if wd is not None:
    weight_decay = tf.multiply(tf.nn.l2_loss(var), wd, name='weight_loss')
    tf.add_to_collection('losses', weight_decay)
  return var

def inference(images, name='m0', reuse=None):
    batch_size = int(images.shape[0])
    images = tf.reshape(images, [-1, IMAGE_SIZE, IMAGE_SIZE, 1])

    # conv1
    with tf.variable_scope(name + '_conv1', reuse=reuse) as scope:
        kernel = _variable_with_weight_decay('weights',
                                             shape=[5, 5, 1, 64],
                                             stddev=5e-2,
                                             wd=0.0)
        conv = tf.nn.conv2d(images, kernel, [1, 1, 1, 1], padding='SAME')
        biases = _variable_on_cpu('biases', [64],
                                  tf.constant_initializer(0.0))
        pre_activation = tf.nn.bias_add(conv, biases)
        conv1 = tf.nn.relu(pre_activation, name=scope.name)

    # pool1
    pool1 = tf.nn.max_pool(conv1, ksize=[1, 3, 3, 1], strides=[1, 2, 2, 1],
                           padding='SAME', name='pool1')
    # norm1
    norm1 = tf.nn.lrn(pool1, 4, bias=1.0, alpha=0.001 / 9.0, beta=0.75,
                      name='norm1')

    # conv2
    with tf.variable_scope(name + '_conv2', reuse=reuse) as scope:
        kernel = _variable_with_weight_decay('weights',
                                             shape=[5, 5, 64, 64],
                                             stddev=5e-2,
                                             wd=0.0)
        conv = tf.nn.conv2d(norm1, kernel, [1, 1, 1, 1], padding='SAME')
        biases = _variable_on_cpu('biases', [64], tf.constant_initializer(0.1))
        pre_activation = tf.nn.bias_add(conv, biases)
        conv2 = tf.nn.relu(pre_activation, name=scope.name)

        # norm2
        norm2 = tf.nn.lrn(conv2, 4, bias=1.0, alpha=0.001 / 9.0, beta=0.75,
                          name='norm2')
        # pool2
        pool2 = tf.nn.max_pool(norm2, ksize=[1, 3, 3, 1],
                               strides=[1, 2, 2, 1], padding='SAME',
                               name='pool2')

    # local3
    with tf.variable_scope(name + '_local3', reuse=reuse) as scope:
        # Move everything into depth so we can perform a single matrix multiply.
        reshape = tf.reshape(pool2, [batch_size, -1])
        dim = reshape.get_shape()[1].value
        weights = _variable_with_weight_decay('weights', shape=[dim, FC_SIZE_1],
                                              stddev=0.04, wd=WEIGHT_DECAY)
        biases = _variable_on_cpu('biases', [FC_SIZE_1],
                                  tf.constant_initializer(0.1))
        local3 = tf.nn.relu(tf.matmul(reshape, weights) + biases,
                            name=scope.name)

    # local4
    with tf.variable_scope(name + '_local4', reuse=reuse) as scope:
        weights = _variable_with_weight_decay('weights',
                                              shape=[FC_SIZE_1, FC_SIZE_2],
                                              stddev=0.04, wd=WEIGHT_DECAY)
        biases = _variable_on_cpu('biases', [FC_SIZE_2],
                                  tf.constant_initializer(0.1))
        local4 = tf.nn.relu(tf.matmul(local3, weights) + biases,
                            name=scope.name)

    # linear layer(WX + b),
    # We don't apply softmax here because
    # tf.nn.sparse_softmax_cross_entropy_with_logits accepts the unscaled logits
    # and performs the softmax internally for efficiency.
    with tf.variable_scope(name + '_softmax_linear', reuse=reuse) as scope:
        weights = _variable_with_weight_decay('weights',
                                              [FC_SIZE_2, NUM_CLASSES],
                                              stddev=1.0/FC_SIZE_2, wd=0.0)
        biases = _variable_on_cpu('biases', [NUM_CLASSES],
                                  tf.constant_initializer(0.0))
        softmax_linear = tf.add(tf.matmul(local4, weights), biases,
                                name=scope.name)

    return softmax_linear


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


def save_weights(sess, dir='models'):
    os.makedirs(dir, exist_ok=True)
    all_vars = tf.trainable_variables()
    with gzip.open(dir + "/mnist_params.pkl.gz", "w") as f:
        pickle.dump(tuple(map(lambda x: x.eval(sess), all_vars)), f)


# def load_weights(sess, dir, model_name='m0'):
#     i = 0
#     filename = dir + '/mnist_params.pkl.gz' if dir else 'mnist_params.pkl.gz'
#     with gzip.open(filename, 'rb') as f:
#         weights = pickle.load(f, encoding='latin1')
#         w1, b1, w2 = tuple(weights[i:i+3])
#         i += 3
#         with tf.variable_scope(model_name, reuse=True):
#             w1_var = tf.get_variable("w1", (IMAGE_PIXELS, HIDDEN_SIZE))
#             b1_var = tf.get_variable("b1", (HIDDEN_SIZE))
#             w2_var = tf.get_variable("w2", (HIDDEN_SIZE, NUM_CLASSES))
#             sess.run([w1_var.assign(w1), b1_var.assign(b1),
#                       w2_var.assign(w2)]

def load_weights(sess, dir, model_name='m0'):
    filename = dir + '/mnist_params.pkl.gz' if dir else 'mnist_params.pkl.gz'
    with gzip.open(filename, 'rb') as f:
        weights = pickle.load(f, encoding='latin1')
        # print(len(weights))
    c1w, c1b, c2w, c2b, l3w, l3b, l4w, l4b, smw, smb = tuple(weights[:10])
    with tf.variable_scope(model_name + '_conv1', reuse=True):
        w_var = tf.get_variable('weights', [5, 5, 1, 64])
        b_var = tf.get_variable("biases", [64])
        sess.run(w_var.assign(c1w))
        sess.run(b_var.assign(c1b))
    with tf.variable_scope(model_name + '_conv2', reuse=True):
        w_var = tf.get_variable('weights', [5, 5, 64, 64])
        b_var = tf.get_variable("biases", [64])
        sess.run(w_var.assign(c2w))
        sess.run(b_var.assign(c2b))
    with tf.variable_scope(model_name + '_local3', reuse=True):
        # w_var = tf.get_variable('weights', [2304, FC_SIZE_1])
        # w_var = tf.get_variable('weights', [4096, FC_SIZE_1])
        w_var = tf.get_variable('weights', [3136, FC_SIZE_1])
        b_var = tf.get_variable("biases", [FC_SIZE_1])
        sess.run(w_var.assign(l3w))
        sess.run(b_var.assign(l3b))
    with tf.variable_scope(model_name + '_local4', reuse=True):
        w_var = tf.get_variable('weights', [FC_SIZE_1, FC_SIZE_2])
        b_var = tf.get_variable("biases", [FC_SIZE_2])
        sess.run(w_var.assign(l4w))
        sess.run(b_var.assign(l4b))
    with tf.variable_scope(model_name + '_softmax_linear', reuse=True):
        w_var = tf.get_variable('weights', [FC_SIZE_2, 10])
        b_var = tf.get_variable("biases", [10])
        sess.run(w_var.assign(smw))
        sess.run(b_var.assign(smb))
