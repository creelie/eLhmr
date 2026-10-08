#!/usr/bin/env python3
"""Validation on equations that have solutions: 2^k (n - 1) = (2^k + m) phi(n), omega(n) = k, p_1 >= 3,
for k = 4 (1 <= m <= 40) and k = 5 (1 <= m <= 85).  Both programs must return the same solutions, namely the
56 listed in data/known_solutions.json, each of which is checked by direct arithmetic.  The totient sieve
(sieve_check.py) confirms independently that the list is complete below 10^8.
Runtime: about 5 minutes for Program 1 and about 80 minutes for Program 2."""
import json, sys, time
sys.path.insert(0, ".")
from math import prod
from tree_search import Search
from tree_enum import run
known = json.load(open("data/known_solutions.json"))
for k, key, mmax in ((4, "S4", 40), (5, "S5", 85)):
    kn = {n for n, _ in known[key]}
    for n, half in known[key]:
        ps = [2 * h + 1 for h in half]      # the file stores the half-gaps (p - 1)/2
        assert prod(ps) == n and len(ps) == k
        phi = prod(p - 1 for p in ps); assert (2**k * (n - 1)) % phi == 0 and 1 <= 2**k * (n - 1) // phi - 2**k <= mmax
    f1 = set(); t0 = time.time()
    for m in range(1, mmax + 1):
        S = Search(k, 2**k + m, 2**k, pmin=3, eps=-1); S.run(); f1 |= {n for n, _ in S.sols}
    print(f"program 1, k={k}: {len(f1)} solutions; equal to the list: {f1 == kn}  ({time.time()-t0:.0f}s)", flush=True)
    f2 = set(); t0 = time.time()
    for m in range(1, mmax + 1):
        _, _, _, sols = run(k, pmin=3, a=2**k + m, b=2**k, eps=-1); f2 |= {n for n, _ in sols}
    print(f"program 2, k={k}: {len(f2)} solutions; equal to the list: {f2 == kn}  ({time.time()-t0:.0f}s)", flush=True)
    assert f1 == kn == f2
