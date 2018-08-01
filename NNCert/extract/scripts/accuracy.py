#Calculate the accuracy of a TF->Coq EMNIST model producing a transcript
#of the form:
# batch 2399 # correct: 88.
# batch 2398 # correct: 91.
# batch 2397 # correct: 94.
# ...
# for a total of 2400 batches of 100 examples each.

# USAGE: python3 accuracy.py < TRANSCRIPT_FILE

import sys

NUM_BATCHES=2400
EXAMPLES_PER_BATCH=100

i=0
total_correct=0
for line in sys.stdin:
    correct = int(line[:-1]) #remove '\n'
    total_correct += int(correct) 
    i += 1

if i != NUM_BATCHES:
    print("WARNING: Read only {i} entries".format(i=i))
    
print("Total correct: {total_correct}\nAccuracy: {accuracy}".format(
    total_correct=total_correct,
    accuracy=float(total_correct)/float(NUM_BATCHES*EXAMPLES_PER_BATCH)))
        
      
