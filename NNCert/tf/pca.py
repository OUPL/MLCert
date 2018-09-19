import numpy as np
import pickle
from sklearn.decomposition import PCA
from dataset_params import choose_dataset, make_dataset

# This file contains code for reducing the dimensionality of the
# EMNIST data using PCA. It uses the PCA implementation provided by
# sklearn which can be installed through pip.

_, _, _, _, _, load_data = choose_dataset('emnist')
train_data, validation_data, test_data = load_data()

# images = np.concatenate([train_data.images, validation_data.images], axis=0)

pca = PCA(n_components=8**2) # d=64

# Fit to training + validation data
# pca.fit(images)

# Fit to validation data only
pca.fit(validation_data.images)

train_images = pca.transform(train_data.images)
validation_images = pca.transform(validation_data.images)
test_images = pca.transform(test_data.images)

print(train_images[0])

with open("emnist/train_reduced.pkl", "wb") as f:
    pickle.dump(make_dataset(train_images, train_data.labels), f)

with open("emnist/validation_reduced.pkl", "wb") as f:
    pickle.dump(make_dataset(validation_images, validation_data.labels), f)

with open("emnist/test_reduced.pkl", "wb") as f:
    pickle.dump(make_dataset(test_images, test_data.labels), f)
