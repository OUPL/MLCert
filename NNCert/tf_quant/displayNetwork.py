import numpy as np

from scipy.misc import imsave
from math import sqrt, floor, ceil

def displayNetwork(A, cols = None, file_name = 'network.jpg', opt_normalize = True):
  """This function visualizes filters in matrix A. Each column of A is a
  filter. We will reshape each column into a square image and visualizes
  on each cell of the visualization panel. 

  Args:
    cols: how many columns are there in the display. Default value is the
      squareroot of the number of columns in A.
    opt_normalize: whether we need to normalize the filter so that all of
      them can have similar contrast. Default value is true.
  """

  # rescale
  A = A - np.mean(A)

  # compute rows, cols
  L, M = A.shape
  sz = int(sqrt(L))
  buf = 1
  if cols is None:
    if floor(sqrt(M)) ** 2 != M:
      n = ceil(sqrt(M))
      while M % n != 0 and n < 1.2 * sqrt(M):
        n = n + 1
      m = ceil(M / n)
    else:
      n = sqrt(M)
      m = n
  else:
    n = cols;
    m = ceil(M / n)

  array = -np.ones((int(buf + m * (sz + buf)), int(buf + n * (sz + buf))), dtype=np.float32)


  k = 0
  for i in range(int(m)):
    for j in range(int(n)):
      if k >= M:
        continue
      clim = np.max(np.abs(A[:,k]))
      cpos = buf + i * (sz + buf)
      rpos = buf + j * (sz + buf)
      if opt_normalize:
        array[cpos : cpos + sz, rpos: rpos + sz] = np.reshape(A[:,k], (sz, sz)) / clim
      else:
        array[cpos : cpos + sz, rpos: rpos + sz] = np.reshape(A[:,k], (sz, sz)) / np.max(np.abs(A))
      k = k + 1

  imsave(file_name, array)

  return array
