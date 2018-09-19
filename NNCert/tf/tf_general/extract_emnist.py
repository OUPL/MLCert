from shared import emnist_load_data
from util import save_pickled_files

save_pickled_files(emnist_load_data(), ['emnist/train.pkl',
                                        'emnist/validation.pkl',
                                        'emnist/test.pkl'])
