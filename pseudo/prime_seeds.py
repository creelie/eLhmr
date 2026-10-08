#!/usr/bin/env python3
"""Seeds for descent_prime.py: the prefixes of coprime_prefixes_k15.pkl (written by coprime_tree.py 15) whose entries
are primes p_1 < ... < p_j with p_i not dividing p_l - 1, defect c = 2B - A > 0 and c p_j < 2B, so that one more entry
can complete them. Writes prime_prefixes_k15.pkl and prints their number and their sum of 1/c."""
import math, pickle
from sympy import isprime

pre = pickle.load(open('coprime_prefixes_k15.pkl', 'rb'))
out = {}
for p, c in pre.items():
    if c <= 0 or not all(isprime(x) for x in p):
        continue
    if any(q % r == 1 for q in p for r in p):
        continue
    if 2 * math.prod(x - 1 for x in p) <= c * p[-1]:
        continue
    out[p] = c
pickle.dump(out, open('prime_prefixes_k15.pkl', 'wb'))
print(len(pre), "prefixes of coprime_tree.py 15;", len(out), "consist of independent primes; sum of 1/c",
      f"{sum(1 / c for c in out.values()):.4e} of {sum(1 / c for p, c in pre.items() if c > 0):.4e}")
