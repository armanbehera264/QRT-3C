#!/bin/python3

import math
import os
import random
import re
import sys



#
# Complete the 'probe' function below.
#
# The function is expected to return a FLOAT_ARRAY.
# The function accepts FLOAT t as parameter.
def probe(t):
    pts = [(0.00, 0.08), (0.08, 0.12), (0.12, 0.10), (0.15, 0.0),
           (0.18, -0.15), (0.20, -0.20), (0.24, -0.29), (0.28, -0.32),
           (0.40, -0.34), (0.48, -0.34), (0.51, 0.0), (0.54, 0.38),
           (0.74, 0.39), (0.78, 0.30), (0.80, 0.24), (0.82, 0.0),
           (0.84, -0.12), (0.92, -0.12), (0.94, 0.0), (0.96, 0.15),
           (1.00, 0.15)]
    for (t0, x0), (t1, x1) in zip(pts, pts[1:]):
        if t <= t1:
            return [x0 + (x1 - x0) * (t - t0) / (t1 - t0)]
    return [pts[-1][1]]

if __name__ == '__main__':
    fptr = open(os.environ['OUTPUT_PATH'], 'w')

    t = float(input().strip())

    result = probe(t)

    fptr.write('\n'.join(map(str, result)))
    fptr.write('\n')

    fptr.close()
