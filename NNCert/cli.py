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

# i/n
def render_progress_bar(i, n, msg=None):
    xs = ['|', '/', '-', '\\']
    progress = int(i / n * 20)
    s = '[' + '█'*progress + colored('.'*(20-progress), 'grey') + '] ' + \
        colored(xs[i//100%(len(xs))], 'magenta')
    if msg:
        s += ' ⊢ ' + msg
    ui.render_in_bottombar(s)

def clear_bottom_bar():
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


def gen_pca():
    questions = [
        inquirer.Text('pca_d',
                      message =
                      'Square root of number of principal components',
                      validate =
                      lambda _, x: 1 <= int(x) <= int(sqrt(784)) )
    ]
    pca_d = int(inquirer.prompt(questions)['pca_d'])
    print('Loading original data...')
    _, load_data = choose_dataset('emnist')
    train_data, valid_data, test_data = load_data('tf/')
    pca = PCA(n_components=pca_d**2)
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
def train_or_eval(do_train=True):
    weights_type, bits = ask_weight_info()
    hidden_sizes = ask_layer_info()
    use_pca = ask_use_pca()

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
            questions = [
                inquirer.Confirm(
                    'old_pca',
                    message='Use existing PCA data (%d principal components)?'
                    % data.images.shape[1])
            ]
            if inquirer.prompt(questions)['old_pca']:
                print('Using existing PCA data.')
            else:
                gen_pca()
        else:
            gen_pca()

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
        i = 0
        if do_train:
            print('Training model...')
            seq = train_model(sess, model, x, y, train_op, loss_op,
                              pred_op, weights, images, labels,
                              batch_size, max_steps, 'tf/models/default/',
                              bits, 1.0, log=False)
            ac = 0.0
            for _, acc in seq:
                i += 1
                render_progress_bar(i, max_steps,
                                    (colored('Accuracy', 'yellow') + ': %0.02f%%') \
                                    % (acc * 100.0))
                ac = acc
            clear_bottom_bar()
            print('Done training model.')
            print('Selecting weights with best accuracy (%.02f%%).' % (acc * 100.0))
        else:
            print('Evaluating model...')
            model.load_weights(sess, 'tf/models/default/', num_bits=bits,
                               pca_d=pca_d)
            acc = evaluate(sess, x, y, pred_op, images, labels, 100,
                           log=False)
            print('acc: %.02f' % acc)


def compile():
    # TODO: copy weights, use compile script, generate empiricalloss
    # config file, and maybe compile the extracted OCaml program
    # (optimization flags?)
    copyfile('tf/models/default/params.pkl.gz', 'params.pkl.gz')

    with gzip.open('params.pkl.gz', 'rb') as f:
        weights = pickle.load(f, encoding='latin1')

    # print(len(weights))
    # _ = [print(w.shape) for w in weights]
    # exit(0)

    # Set the type of weights based on the presence of shift/scale.
    weights_type = 'float' if len(weights) == 2 else 'quantized'
    if weights_type == 'float':
        bits = 16
    else:
        bits = len(weights[0][0][0])

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


def extract():
    call(['touch', 'out.v'])
    call(['make'])
    print('Extracting model...')
    call(['coqc', '-R', '..', 'MLCert', '-w', 'none', 'empiricalloss.v'])
    print('Done extracting model.')


def evaluate():
    # TODO: give option to either run the OCaml batch evaluation
    # program or run one of the other validation scripts.
    print('evaluate')

    with gzip.open('params.pkl.gz', 'rb') as f:
        weights = pickle.load(f, encoding='latin1')

    num_batches = 2000 if load_pickled('pca.pkl') else 2400

    # TODO: need to generate different batch data sometimes.. (PCA)
    # if not Path('extract/batches/batch_' + str(num_batches-1)).is_file():
    pca = load_pickled('pca.pkl')
    questions = [
        inquirer.Confirm(
            'make_batches',
            message='Generate batch data?')
    ]
    if inquirer.prompt(questions)['make_batches']:
        call(['python3', 'tf/make_simple_data.py', str(num_batches),
              str(pca), 'False', 'tf/emnist', 'extract/batches'])

    # print('Batch data is missing. Generating it now..')
    # call(['python3', 'tf/make_simple_data.py', str(num_batches), 'False', 'tf'])
    # print('Done generating batches.')

    call(['rm', 'extract/batch_test.mli'])
    # call(['ocamlopt', '-o', 'extract/batch_test', 'extract/batch_test.ml'])
    print('Compiling OCaml executable...')
    call(['ocamlopt', '-inline', '1000', '-o', 'extract/batch_test',
          'extract/batch_test.ml'])
    print('Running evaluation...')
    call(['extract/scripts/train_err', 'extract/batch_test', 'extract/log.txt',
          'extract/batches', str(num_batches), str(5)])
    call(['python3', 'extract/scripts/accuracy.py', 'extract/log.txt'])



while True:
    # User entry point.
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

# TODO: maybe support little script files in XML or something so this
# program can just be pointed to one of those files to execute
# specified actions and then exit. Maybe just piping regular inputs to
# stdin would work?
