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
import gzip, pickle
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
from util import save_pickled_files


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
                      message = 'Precision? (2-8)',
                      validate = lambda _, x: 2 <= int(x) <= 8 )
    ]
    return int(inquirer.prompt(questions)['bits'])

def ask_weight_info():
    questions = [
        inquirer.List('weights_type',
                      message = 'Float or quantized?',
                      choices = ['Float',
                                 'Quantized'])
    ]
    weights_type = inquirer.prompt(questions)['weights_type'].lower()
    bits = 16 if weights_type == 'float' else ask_bits()

    return weights_type, bits

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
    

# For now we only allow training but that could change.
def train_or_eval(do_train=True):
    weights_type, bits = ask_weight_info()
    use_pca = ask_use_pca()

    if use_pca:
        questions = [
            inquirer.Confirm(
                'gen_pca',
                message='Generate PCA data?')
        ]
        if inquirer.prompt(questions)['gen_pca']:
            questions = [
                inquirer.Text('pca_d',
                              message =
                              'Square root of number of principal components?',
                              validate =
                              lambda _, x: 1 <= int(x) <= int(sqrt(784)) )
            ]
            pca_d = int(inquirer.prompt(questions)['pca_d'])
            print('Loading original data...')
            _, _, _, _, load_data = choose_dataset('emnist')
            train_data, validation_data, test_data = load_data('tf')
            pca = PCA(n_components=pca_d**2)
            # Fit to validation data only
            print('Fitting to validation data...')
            pca.fit(validation_data.images)
            train_images = pca.transform(train_data.images)
            validation_images = pca.transform(validation_data.images)
            test_images = pca.transform(test_data.images)
            print('Writing PCA transformed data to disk...')
            save_pickled_files(['tf/emnist/train_pca.pkl',
                                'tf/emnist/validation_pca.pkl',
                                'tf/emnist/test_pca.pkl'],
                               [make_dataset(images, labels)
                                for images, labels in
                                zip([train_images,
                                     validation_images,
                                     test_images],
                                    [train_data.labels,
                                     validation_data.labels,
                                     test_data.labels])])
        else:
            print('Using existing PCA data.')

    # Choose between float and quantized models.
    model = float_model if weights_type == 'float' else quantized_model

    # Load parameters and data for the chosen dataset.
    save_images, load_data \
        = choose_dataset('emnist' + ('' if use_pca else '_pca'))
    print ('Loading data...')
    train_data, validation_data, test_data = load_data('tf/')

    # Choose which set to use (train, test, etc.).
    # We pass 3 for combined train+validation if PCA isn't being used,
    # otherwise we pass 2 to use only training data.
    images, labels = choose_images_labels(train_data, validation_data,
                                          test_data,
                                          3 if use_pca else 2)
    example_shape = images.shape[1:]
    input_size = reduce(mul, example_shape, 1)

    with tf.Graph().as_default():

        # Build all of the ops.
        print("building computation graph...")

        # Choose between a few different values for learning rate and
        # stuff depending on the options chosen by the user.
        learning_rate, max_steps, decay_step, decay_factor = choose_hypers(
            weights_type, bits)
        batch_size = 100

        x, y, weights, logits, loss_op, pred_op, train_op = build_ops(
            100, bits, learning_rate, decay_step, decay_factor,
            model, input_size)

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

    # Set the type of weights based on the presence of shift/scale.
    weights_type = 'float' if len(weights) == 2 else 'quantized'
    if weights_type == 'float':
        bits = 16
    else:
        bits = len(weights[0][0][0])

    # We don't need to know the PCA dimensionality information here
    # because the compile script just looks at dimensions of the
    # weights.
    # weights_type, bits = ask_weight_info()

    # Run the compile script
    if weights_type == 'float':
        if bits != 16:
            print('Sorry, only 16-bit float is supported at the moment.')
            return
        call(['python3', 'compile_kernel.py', 'params.pkl.gz'])
    else:
        call(['python3', 'compile_quantized_kernel.py', 'params.pkl.gz',
              str(bits)])

    print('compile')


def evaluate():
    # TODO: give option to either run the OCaml batch evaluation
    # program or run one of the other validation scripts.
    print('evaluate')


while True:
    # User entry point.
    questions = [
        inquirer.List('action',
                      message='What do you want to do?',
                      choices=['Train a TensorFlow model',
                               'Compile TensorFlow model to Coq',
                               'Evaluate a Coq model',
                               'Exit'])
    ]

    # Branch on the user's response.
    answers = inquirer.prompt(questions)
    { 'train': lambda: train_or_eval(True),
      'compile': compile,
      'evaluate': evaluate,
      'exit': lambda: exit(0) } [answers['action'].split()[0].lower()]()
