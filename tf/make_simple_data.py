import gzip, pickle, os.path, sys
import numpy as np
import struct

# Generate batch files to be loaded by Coq/OCaml.

# Number of bits (e.g., 16 or 32) per floating-point parameter
N = 16
BATCH_SIZE = 100

num_batches = int(sys.argv[1])

# with open('emnist/all.pkl', 'rb') as f:
with open('emnist/test.pkl', 'rb') as f:
# with gzip.open('small/test.pkl.gz', 'rb') as f:
    data = pickle.load(f, encoding='latin1')

images = data.images
labels = data.labels
print(images.shape)

# This function stolen from code posted to:
# https://stackoverflow.com/questions/16444726/binary-representation-of-float-in-python-bits-not-hex
# def binary(num):
#     return ''.join(bin(c).replace('0b', '').rjust(8, '0')
#                    for c in struct.pack('!f', num))

def binary(f):
    if N == 32:
        return ''.join(bin(c).replace('0b', '').rjust(8, '0')
                       for c in struct.pack('!f', np.float32(f).item()))
    elif N == 16:
        return str(bin(np.float16(f).view('H'))[2:].zfill(16))
    else:
        return None
        
# END stolen

# Indices record the '1' bits.
def float_to_bin(f):
    # b = binary(float_cast(f).item())
    # b = b[:N][::-1]
    b = binary(f)[::-1]
    l = zip(list(range(N)), [i for i in b])
    # Just the nonzero indices
    return list(map(lambda p: p[0], filter(lambda x: x[1] == '1', l)))

def encode_image(image):
    return list(filter(lambda p: p[1],
                       [(i, float_to_bin(image[i]))
                   for i in range(image.shape[0])]))

os.makedirs('../extract/batches', exist_ok=True)
# for i in range(0, images.shape[0], BATCH_SIZE):
for i in range(0, num_batches * BATCH_SIZE, BATCH_SIZE):
    batch_images = images[i:i+BATCH_SIZE,:]
    batch_labels = labels[i:i+BATCH_SIZE]
    print(batch_labels)
    encoded_images = list(map(encode_image, batch_images))
    with open('../extract/batches/batch_' + str(i//BATCH_SIZE), 'w') as f:
        for j in range(BATCH_SIZE):
            encoded_image = encoded_images[j]
            f.write(str(batch_labels[j]) + ' ')
            for (x, bits) in encoded_image:
                f.write(str(x) + ' ' + str(len(bits)) + ' ' + \
                        ' '.join(map(str, bits)) + ' ')
            f.write('\n')


from ast import literal_eval

# x = 1.0
# x = 5.88895399373e-39
# x = 1.0009765625
# x = -2.0
# x = 0.00784301757812
x = 65504
print(x)

print(float_to_bin(x))

# https://stackoverflow.com/a/33452578/6751010
print(bin(np.float16(x).view('H'))[2:].zfill(16))

# b = '{:016b}'.format(struct.unpack('<H', np.float16(x).tobytes())[0])
if N == 16:
    b = '{:016b}'.format(struct.unpack('<H', np.float16(x).tobytes())[0])
else:
    b = '{:032b}'.format(struct.unpack('<I', np.float32(x).tobytes())[0])
print(b)

if N == 16:
    # b = b + '0'*16
    b = '0'*16 + b
f = int(b, 2)
# print(struct.unpack('f', struct.pack('I', f))[0])
print(struct.unpack('f', struct.pack('I', f))[0])
# f = struct.unpack('f', b)
# print(f)
