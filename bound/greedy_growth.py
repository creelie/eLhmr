"""Table 1 of the paper (Section 2.2): the independent sets chosen one prime at a time
from the primes from 5 on ('all') and from the primes p = 2 (mod 3) from 5 on ('mod3'),
with the number of elements up to x and the product of p/(p-1) over them, for x = 10^3, ..., 10^8.

Usage: python3 greedy_growth.py 1e8 all   |   python3 greedy_growth.py 1e8 mod3
"""
import math
import sys

import numpy as np

X = int(float(sys.argv[1]))
mode = sys.argv[2]
isp = np.ones(X + 1, dtype=bool)
isp[:2] = False
for p in range(2, int(X ** 0.5) + 1):
    if isp[p]:
        isp[p * p::p] = False
excluded = np.zeros(X + 1, dtype=bool)   # excluded[q]: q = 1 (mod p) for a chosen p
marks = [10 ** e for e in range(3, 10) if 10 ** e <= X]
logP, count, mi, out = 0.0, 0, 0, {}
for q in np.nonzero(isp)[0]:
    q = int(q)
    while mi < len(marks) and q > marks[mi]:
        out[marks[mi]] = (count, math.exp(logP))
        mi += 1
    if q < 5 or (mode == 'mod3' and q % 3 != 2) or excluded[q]:
        continue
    count += 1
    logP += math.log(q / (q - 1))
    excluded[1 + q::q] = True
while mi < len(marks):
    out[marks[mi]] = (count, math.exp(logP))
    mi += 1
xs = sorted(out)
for x in xs:
    c, P = out[x]
    print("x = %10d  loglog x = %.3f  elements %8d  product %.4f" % (x, math.log(math.log(x)), c, P))
ll = [math.log(math.log(x)) for x in xs]
pr = [out[x][1] for x in xs]
slope, icpt = np.polyfit(ll, pr, 1)
res = max(abs(p - (slope * l + icpt)) for l, p in zip(ll, pr))
print("least-squares line: product = %.4f * loglog x + %.4f, largest deviation %.4f" % (slope, icpt, res))
