import sys
sys.path.insert(0, './tf')

from pathlib import Path
from git import Repo
import inquirer

from dataset_params import choose_dataset
from train import train_model
from eval import evaluate
import float_model, quantized_model
from shared import build_ops, choose_images_labels, emnist_load_data, \
    init_session
from util import save_pickled_files


ui = inquirer.render.console.ConsoleRender()


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
                           emnist_load_data('tf'))


def train_or_eval(do_train=True):
    questions = [
        inquirer.List('weights_type',
                      message = 'Float or quantized?',
                      choices = ['Float',
                                 'Quantized'])
    ]
    weights_type = inquirer.prompt(questions)['weights_type'].lower()

    questions = [
        inquirer.List('bits',
                      message = 'Precision?',
                      choices = ['16', '32'])
        if weights_type == 'float' else
        inquirer.Text('bits',
                      message = 'Precision? (2-8)',
                      validate = lambda _, x: 2 <= int(x) <= 8 )
    ]
    bits = int(inquirer.prompt(questions)['bits'])

    questions = [inquirer.Confirm('pca', message = 'Do PCA transform?')]
    if inquirer.prompt(questions)['pca']:
        questions = [
            inquirer.Text('pca_d',
                          message =
                          'Square root of number of principal components?',
                          validate = lambda _, x: 1 <= int(x) <= 784 )
        ]
        pca_d = int(inquirer.prompt(questions)['pca_d'])
    else: pca_d = 0

    # TODO: ask if it is necessary to generate the PCA transformed
    # data (not necessary if we already did and the dimensionality
    # hasn't changed)

    # Choose between float and quantized models.
    model = float_model if weights_type == 'float' else quantized_model

    # Load parameters and data for the chosen dataset.
    save_images, NUM_CLASSES, IMAGE_SIZE, example_shape, load_data \
        = choose_dataset('emnist' + ('' if pca_d == 0 else '_reduced'),
                         pca_d)
    print ('Loading data...')
    train_data, validation_data, test_data = load_data()

    # Choose which set to use (train, test, etc.).
    # We pass 3 for combined train+validation.
    images, labels = choose_images_labels(train_data, validation_data,
                                          test_data, 3)

    with tf.Graph().as_default():

        # Build all of the ops.
        print("building computation graph...")
        # TODO: choose between a few different values for learning
        # rate and stuff depending on the options chosen by the user
        x, y, weights, logits, loss_op, pred_op, train_op = build_ops(
            100, bits, pca_d, 0.1, 25000, 0.1, model, example_shape)

        # Create session and initialize variables.
        sess = init_session()

        # Go.
        if do_train:
            seq = train_model(sess, model, x, y, train_op, loss_op,
                              pred_op, weights, images, labels,
                              100, 50000, 'tf/models/default/',
                              bits, 1.0, log=False)
            for _, acc in seq:
                # TODO: render progress bar here instead
                print('acc: %.02f' % acc)
        else:
            model.load_weights(sess, 'tf/models/default/', num_bits=bits,
                               pca_d=pca_d)
            acc = evaluate(sess, x, y, pred_op, images, labels, 100,
                           log=False)
            print('acc: %.02f' % acc)


    

def compile():
    # TODO: copy weights, use compile script, use sed on empiricalloss
    # template file, and maybe compile the extracted OCaml program
    # (optimization flags?)
    print('compile')


def evaluate():
    # TODO: give option to either run the OCaml batch evaluation
    # program or run one of the other validation scripts.
    print('evaluate')


# User entry point.
questions = [
    inquirer.List('action',
                  message='What do you want to do?',
                  choices=['Train a TensorFlow model',
                           'Compile a TensorFlow model to Coq',
                           'Evaluate a Coq model'])
]

# Branch on the user's response.
answers = inquirer.prompt(questions)
{ 'train': train,
  'compile': compile,
  'evaluate': evaluate } [answers['action'].split()[0].lower()]()
