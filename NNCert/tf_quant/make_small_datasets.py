import gzip, pickle, os.path
import numpy as np
import tensorflow as tf
from tensorflow.contrib.learn.python.learn.datasets.mnist import DataSet
def make_dataset(images, labels):
    return DataSet(images, labels, reshape=False, dtype=tf.uint8)

SIZE = 16


# with open('emnist/train.pkl', 'rb') as f:
#     train = pickle.load(f, encoding='latin1')
# with open('emnist/validation.pkl', 'rb') as f:
#     validation = pickle.load(f, encoding='latin1')
# with open('emnist/test.pkl', 'rb') as f:
#     test = pickle.load(f, encoding='latin1')

# train_images = train.images
# validation_images = validation.images
# test_images = test.images

# small_train = []
# small_validation = []
# small_test = []

# for i in range(train_images.shape[0]):
#     small_train.append(train_images[i][:SIZE])
# for i in range(validation_images.shape[0]):
#     small_validation.append(validation_images[i][:SIZE])
# for i in range(test_images.shape[0]):
#     small_test.append(test_images[i][:SIZE])

# small_train = np.array(small_train)
# small_validation = np.array(small_validation)
# small_test = np.array(small_test)

small_train_images = np.random.random([50000, 16])
small_validation_images = np.random.random([10000, 16])
small_test_images = np.random.random([10000, 16])

small_train_labels = np.random.random_integers(0, 1, size=50000)
small_validation_labels = np.random.random_integers(0, 1, size=10000)
small_test_labels = np.random.random_integers(0, 1, size=10000)

small_train = make_dataset(small_train_images, small_train_labels)
small_validation = make_dataset(small_validation_images, small_validation_labels)
small_test = make_dataset(small_test_images, small_test_labels)

print(small_train_images.shape)
print(small_validation_images.shape)
print(small_test_images.shape)

os.makedirs('small/', exist_ok=True)
with gzip.open('small/train.pkl.gz', 'w') as f:
    pickle.dump(small_train, f)
with gzip.open('small/validation.pkl.gz', 'w') as f:
    pickle.dump(small_validation, f)
with gzip.open('small/test.pkl.gz', 'w') as f:
    pickle.dump(small_test, f)

with gzip.open('test_images.pkl.gz', 'w') as f:
    pickle.dump(small_test_images, f)
