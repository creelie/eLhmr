#!/usr/bin/env python3
"""Checks the data for the fifteen long terminal nodes of the case k = 14 of n - 1 = 2 phi(n) (Table 3 of the paper):
for each prefix p_1..p_12, recompute A, B, C = 2B - A, the interval [lo, hi] for p_13 and D = 2AB - C, and verify that
the stored factorisation multiplies out to D and that every stored factor passes the primality test.
Also prints the level profile.  Runtime: seconds."""
import json, sys
sys.path.insert(0, ".")
from math import prod
from fractions import Fraction as Fr
from sympy import isprime
from tree_search import Search
d = json.load(open("data/k14_data.json"))
print("level profile, k = 14:", d["levels"][:13])
S = Search(14, 2, 1, pmin=5, eps=-1)
for h in d["hard_leaves"]:
    ch = h["chain"]; A = prod(ch); B = prod(p - 1 for p in ch); C = 2 * B - A; D = 2 * A * B - C
    P = Fr(A, B); hi, lo = S.bounds(S.mu / P, P, B, ch[-1], 2); lo = max(lo, ch[-1] + 1)
    f = {int(p): e for p, e in h["D_factorization"].items()}
    assert (C, D, lo, hi) == (h["C"], h["D"], h["lo"], h["hi"])
    assert prod(p ** e for p, e in f.items()) == D and all(isprime(p) for p in f)
    print(f"{ch}: width {hi - lo:>9d}, D has {len(str(D))} digits, factors {sorted(f)}")
print("all fifteen certificates check.")
