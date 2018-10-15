#!/usr/bin/env python3

import sys
sys.path.insert(0, './tf')

from math import sqrt
from functools import reduce
from operator import mul
from pathlib import Path
from git import Repo
import inquirer
import numpy as np
import tensorflow as tf
import gzip, os, pickle
from sklearn.decomposition import PCA
from termcolor import colored
from shutil import copyfile
from subprocess import call
import time

from dataset_params import choose_dataset
from train import train_model
from eval import evaluate
import float_model, quantized_model
from shared import build_ops, choose_images_labels, emnist_load_data, \
    init_session, make_dataset
from util import load_pickled, save_pickled, save_pickled_files

# Disable TensorFlow debugging logs.
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'

ui = inquirer.render.console.ConsoleRender()

# Disabling the progress bar can be useful if you want to pipe output
# to a file or something.
RENDER_PROGRESS_BAR = True


# i/n
def render_progress_bar(i, n, msg=None):
    if not RENDER_PROGRESS_BAR: return
    xs = ['|', '/', '-', '\\']
    progress = int(i / n * 20)
    s = '[' + '█'*progress + colored('.'*(20-progress), 'grey') + '] ' + \
        colored(xs[i//100%(len(xs))], 'magenta')
    if msg:
        s += ' ⊢ ' + msg
    ui.render_in_bottombar(s)

def clear_bottom_bar():
    if RENDER_PROGRESS_BAR:
        ui.render_in_bottombar('')


if not Path('tf/emnist/test.pkl').is_file():
    questions = [
        inquirer.Confirm(
            'download',
            message='EMNIST data is missing. Download it now?')
    ]
    if inquirer.prompt(questions)['download']:
        print('Downloading compressed EMNIST data...')
        try:
            Repo.clone_from('https://github.com/bagnalla/emnist.git',
                            'tf/emnist')
        except:
            print('Warning: directory \'tf/emnist\' already exists. \
Assuming the files have already been downloaded.')
        print('Extracting EMNIST data...')
        print('Warning: this takes several minutes and may use up to \
6GB of memory')
        save_pickled_files(['tf/emnist/train.pkl',
                            'tf/emnist/validation.pkl',
                            'tf/emnist/test.pkl'],
                           emnist_load_data('tf/'))
        print()


# Choose learning rate, decay_step, and decay_factor.
def choose_hypers(weights_type, bits):
    return (0.01 if bits == 2 else 0.1), 50000, 25000, 0.1

def ask_bits():
    questions = [
        inquirer.Text('bits',
                      message = 'Precision (2-8)',
                      validate = lambda _, x: 2 <= int(x) <= 8 )
    ]
    return int(inquirer.prompt(questions)['bits'])

def ask_weight_info():
    questions = [
        inquirer.List('weights_type',
                      message = 'Float or quantized',
                      choices = ['Float',
                                 'Quantized'])
    ]
    weights_type = inquirer.prompt(questions)['weights_type'].lower()
    bits = 16 if weights_type == 'float' else ask_bits()
    return weights_type, bits

# def ask_layer_info():
#     questions = [
#         inquirer.Text('layers',
#                       message = 'Number of hidden layers',
#                       validate = lambda _, x: 0 <= int(x) )
#     ]
#     n = int(inquirer.prompt(questions)['layers'])
#     return [inquirer.prompt(
#         [inquirer.Text('layer_size',
#                        message=s,
#                        validate=lambda _, x : 1 <= int(x))])['layer_size']
#             for s in ['Layer %d size' % i for i in range(n)]]

# quantized_model.py doesn't support more than one layer at the moment
# (probably doesn't support 0 hidden layers either), but it shouldn't
# be hard to change. Anyway, for now we only allow a single hidden
# layer.
def ask_layer_info():
    return [inquirer.prompt(
        [inquirer.Text('layer_size',
                       message='Hidden layer size',
                       validate=lambda _, x : 1 <= int(x))])['layer_size']]


def ask_use_pca():
    questions = [inquirer.Confirm('pca', message = 'Use PCA?')]
    return inquirer.prompt(questions)['pca']
    # if inquirer.prompt(questions)['pca']:
    #     questions = [
    #         inquirer.Text('pca_d',
    #                       message =
    #                       'Square root of number of principal components?',
    #                       validate = lambda _, x: 1 <= int(x) <= 784 )
    #     ]
    #     return int(inquirer.prompt(questions)['pca_d'])
    # else: return 0


def gen_pca(pca_d=None):
    if pca_d is None:
        questions = [
            inquirer.Text('pca_d',
                          message =
                          'Number of principal components',
                          validate =
                          lambda _, x: 1 <= int(x) <= int(784) )
        ]
        pca_d = int(inquirer.prompt(questions)['pca_d'])
    print('Loading original data...')
    _, load_data = choose_dataset('emnist')
    train_data, valid_data, test_data = load_data('tf/')
    print(pca_d)
    pca = PCA(n_components=pca_d)
    # Fit to validation data only
    print('Fitting to validation data...')
    pca.fit(valid_data.images)
    train_images = pca.transform(train_data.images)
    valid_images = pca.transform(valid_data.images)
    test_images = pca.transform(test_data.images)
    print('Writing PCA transformed data to disk...')
    save_pickled_files(['tf/emnist/train_pca.pkl',
                        'tf/emnist/validation_pca.pkl',
                        'tf/emnist/test_pca.pkl'],
                       [make_dataset(images, labels)
                        for images, labels in
                        zip([train_images, valid_images, test_images],
                            [train_data.labels, valid_data.labels,
                             test_data.labels])])


# For now we only allow training but that could change.
def train_or_eval(do_train=True, weights_type_bits=None, hidden_sizes=None,
                  use_pca=None, use_old_pca=None, pca_d=None):
    weights_type, bits = ask_weight_info() if weights_type_bits is None \
                         else weights_type_bits
    hidden_sizes = ask_layer_info() if hidden_sizes is None else hidden_sizes
    use_pca = ask_use_pca() if use_pca is None else use_pca

    # TODO: need to ask for the number of hidden layers and their
    # sizes. When compiling / evaluating, we should be able to get
    # that information by looking at the weights, but that might mess
    # with our current method of determining whether the weights are
    # quantized or not. An easy fix is probably to actually check for
    # shift/scale values (maybe by looking at the shape of where they
    # should be) instead of only looking at the length of the weights
    # tuple.

    if use_pca:
        # Check if any PCA data exists.
        if Path('tf/emnist/test_pca.pkl').is_file():
            data = load_pickled('tf/emnist/test_pca.pkl')
            if use_old_pca:
                print('Using existing PCA data.')
            else:
                if use_old_pca is None:
                    questions = [
                        inquirer.Confirm(
                            'old_pca',
                            message='Use existing PCA data (%d principal components)?'
                            % data.images.shape[1])
                    ]
                    if inquirer.prompt(questions)['old_pca']:
                        print('Using existing PCA data.')
                    else: gen_pca(pca_d)
                else:
                    if use_old_pca: print('Using existing PCA data.')
                    else: gen_pca(pca_d)
        else:
            if use_old_pca:
                print('train_or_eval error: use_old_pca is set but there \
is no existing PCA data')
                exit(-1)
            else: gen_pca(pca_d)

    # Write PCA flag to disk so we can easily check later whether PCA
    # is being used or not (so we use the appropriate number of
    # batches during evaluation).
    save_pickled('pca.pkl', use_pca)

    # Choose between float and quantized models.
    model = float_model if weights_type == 'float' else quantized_model

    # Load parameters and data for the chosen dataset.
    _, load_data \
        = choose_dataset('emnist' + ('_pca' if use_pca else ''))
    print('Loading data...')
    train_data, validation_data, test_data = load_data('tf/')

    # Choose which set to use (train, test, etc.).
    # We pass 3 for combined train+validation if PCA isn't being used,
    # otherwise we pass 2 to use only training data.
    images, labels = choose_images_labels(train_data, validation_data,
                                          test_data,
                                          2 if use_pca else 3)
    example_shape = images.shape[1:]
    input_size = reduce(mul, example_shape, 1)

    with tf.Graph().as_default():

        # Build all of the ops.
        print("Initializing...")

        # Choose between a few different values for learning rate and
        # stuff depending on the options chosen by the user.
        learning_rate, max_steps, decay_step, decay_factor = choose_hypers(
            weights_type, bits)
        batch_size = 100

        x, y, weights, logits, loss_op, pred_op, train_op = build_ops(
            100, bits, learning_rate, decay_step, decay_factor,
            model, input_size, hidden_sizes)

        # Create session and initialize variables.
        sess = init_session()

        # Go.
        if do_train:
            print('Training model...')
            seq = train_model(sess, model, x, y, train_op, loss_op,
                              pred_op, weights, images, labels,
                              batch_size, max_steps, 'tf/models/default/',
                              bits, 1.0, log=False)
            i = 0
            for _, acc in seq:
                i += 1
                render_progress_bar(i, max_steps,
                                    (colored('Accuracy', 'yellow') + ': %0.02f%%') \
                                    % (acc * 100.0))
            clear_bottom_bar()
            print('Done training model.')
            print('Selecting weights with best accuracy (%.02f%%).' % (acc * 100.0))
            print(str(acc))
        else:
            print('Evaluating model...')
            model.load_weights(sess, 'tf/models/default/', num_bits=bits,
                               pca_d=pca_d)
            acc = evaluate(sess, x, y, pred_op, images, labels, 100,
                           log=False)
            print('acc: %.02f' % acc)


def compile():
    # Copy weights from tf directory. Not really necessary but whatever.
    copyfile('tf/models/default/params.pkl.gz', 'params.pkl.gz')

    # Load the weights.
    with gzip.open('params.pkl.gz', 'rb') as f:
        weights = pickle.load(f, encoding='latin1')

    # Determine the type of weights based on the presence of
    # shift/scale values. NOTE: if we support different numbers of
    # hidden layers later then this will have to change to actually
    # look for the shift/scale values.
    weights_type = 'float' if len(weights) == 2 else 'quantized'
    bits = 16 if weights_type == 'float' else len(weights[0][0][0])

    # We don't need to know the PCA dimensionality information here
    # because the compile script just looks at dimensions of the
    # weights.

    print('type: ' + weights_type)
    print('bits: %d' % bits)

    # Run the compile script
    if weights_type == 'float':
        if bits != 16:
            print('Sorry, only 16-bit float is supported at the moment.')
            return
        call(['python3', 'compile_kernel.py', 'params.pkl.gz'])
    else:
        call(['python3', 'compile_quantized_kernel.py', 'params.pkl.gz',
              str(bits)])

    print('Done compiling to Coq.')


def extract():
    print('Extracting model...')
    call(['touch', 'out.v'])
    call(['make'])
    call(['coqc', '-R', '..', 'MLCert', '-w', 'none', 'empiricalloss.v'])
    print('Done extracting model.')


def evaluate(gen_batches=None):
    with gzip.open('params.pkl.gz', 'rb') as f:
        weights = pickle.load(f, encoding='latin1')

    num_batches = 2000 if load_pickled('pca.pkl') else 2400

    # TODO: need to generate different batch data sometimes.. (PCA)
    # if not Path('extract/batches/batch_' + str(num_batches-1)).is_file():
    pca = load_pickled('pca.pkl')
    if gen_batches is None:
        questions = [
            inquirer.Confirm(
                'make_batches',
                message='Generate batch data?')
        ]
        gen_batches = inquirer.prompt(questions)['make_batches']
    if gen_batches:
        call(['python3', 'tf/make_simple_data.py', str(num_batches),
              str(pca), 'False', 'tf/emnist', 'extract/batches'])

    # print('Batch data is missing. Generating it now..')
    # call(['python3', 'tf/make_simple_data.py', str(num_batches), 'False', 'tf'])
    # print('Done generating batches.')

    call(['rm', 'extract/batch_test.mli'])
    print('Compiling OCaml executable...')
    call(['ocamlopt', '-o', 'extract/batch_test', 'extract/batch_test.ml'])
    print('Running evaluation...')
    logfile = 'extract/log_' + str(time.time()) + '.txt'
    call(['extract/scripts/train_err', 'extract/batch_test', logfile,
          'extract/batches', str(num_batches), '5'])
    call(['python3', 'extract/scripts/accuracy.py', str(num_batches)],
         stdin=open(logfile, 'r'))


def eat(inputs):
    if not inputs:
        print('error: expected another input')
        exit(-1)
    return inputs[0], inputs[1:]

def mapFst(f, p):
    return f(p[0]), p[1]

def boolOfString(s):
    return True if s.lower() == 'true' else False

def interp_train(inputs):
    weights_type, inputs = eat(inputs)
    if weights_type == 'quantized':
        bits, inputs = mapFst(int, eat(inputs))
    else: bits = 16
    hidden_sizes, inputs = mapFst(lambda x: [int(x)], eat(inputs))
    use_pca, inputs = mapFst(boolOfString, eat(inputs))
    if use_pca:
        use_old_pca, inputs = mapFst(boolOfString, eat(inputs))
        if not use_old_pca:
            pca_d, inputs = mapFst(int, eat(inputs))
        else: pca_d = None
    else: use_old_pca, pca_d = None, None

    train_or_eval(True, weights_type_bits=(weights_type, bits),
                  hidden_sizes=hidden_sizes, use_pca=use_pca,
                  use_old_pca=use_old_pca, pca_d=pca_d)
    interp(inputs)

def interp_compile(inputs):
    compile()
    interp(inputs)

def interp_extract(inputs):
    extract()
    interp(inputs)

def interp_evaluate(inputs):
    gen_batches, inputs = mapFst(boolOfString, eat(inputs))
    evaluate(gen_batches)
    interp(inputs)

def interp(inputs):
    if not inputs: return 0
    { 'train': interp_train,
      'compile': interp_compile,
      'evaluate': interp_evaluate,
      'extract': interp_extract,
      'exit': lambda _: 0 } [inputs[0]](inputs[1:])


# Entry point.
# If a command script is given, execute it and exit. Otherwise, run
# the interactive loop.
if len(sys.argv) > 1:
    with open(sys.argv[1], 'r') as f:
        exit(interp(f.read().lower().split()))
else:
    while True:
        questions = [
            inquirer.List('action',
                          message='Action',
                          choices=['Train a TensorFlow model',
                                   'Compile TensorFlow model to Coq',
                                   'Extract Coq model to OCaml',
                                   'Evaluate extracted model',
                                   'Exit'])
        ]
        
        # Branch on the user's response.
        { 'train': lambda: train_or_eval(True),
          'compile': compile,
          'evaluate': evaluate,
          'extract': extract,
          'exit': lambda: exit(0) } \
          [inquirer.prompt(questions)['action'].split()[0].lower()]()
