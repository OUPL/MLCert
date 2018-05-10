# A class for generating minibatches. Uses sampling without
# replacement. Returns batches of indices for each minibatch.

import numpy as np


class batch_gen(object):
    def __init__(self, batch_size, num_indices, distribution=None,
                 replace=False, max_batches=-1):
        self.batch_size = batch_size
        self.num_indices = num_indices
        self.indices = np.array(range(num_indices))
        self.max_batches = max_batches
        self.counter = 0
        self.distribution = distribution
        self.replace = replace

    def __iter__(self):
        return self

    def __next__(self):
        return self.next()

    def next(self):
        self.counter += 1
        if self.max_batches >= 0 and self.counter > self.max_batches:
            raise StopIteration()
        if self.replace:
            return np.random.choice(self.indices, self.batch_size, replace=True,
                                    p=self.distribution)
        elif self.indices.shape[0] < self.batch_size:
            acc = np.array(self.indices)
            self.indices = np.array(range(num_indices))
            return np.append(acc, np.random.choice(
                self.indices, self.batch_size - acc.shape[0], replace=False))
        else:
            return np.random.choice(self.indices, self.batch_size,
                                    replace=False)
