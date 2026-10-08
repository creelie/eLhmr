#!/usr/bin/env python3
"""Theorem 9.3 (ii), first program: for k <= 15 no odd integers 5 <= x_1 < ... < x_k, none divisible by 3, with
x_1, ..., x_{k-3} prime, satisfy  x_1 ... x_k + eps = 2 (x_1 - 1) ... (x_k - 1).

The prime prefixes x_1 < ... < x_{k-3} with their exact intervals for x_{k-2} are the nodes at depth k - 3 of the
search of Theorems 1.1 and 1.4 (lastthree.frontier(k, 5, 2, 1, eps, 3)).  Below each of them tail3 (mode 3) takes every
odd t = x_{k-2} of the interval with 3 not dividing t and gcd(t, x_i - 1) = gcd(x_i, t - 1) = 1, prime or not, and finds
all integer completions (t, p, q).  Completions with 3 | p or 3 | q are listed separately.
usage: prime_prefixes.py k eps [part nparts]      (for k = 15 run parts 0..3 of 4 in parallel)"""
import sys
from tail3lib import L, line_for, run
k, eps = int(sys.argv[1]), int(sys.argv[2])
part, nparts = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
fr = [[list(map(int, c)), int(lo), int(hi)] for c, A, B, lo, hi in L.frontier(k, 5, 2, 1, eps, 3)]
fr.sort()
fr = fr[part::nparts]
lines = [line_for(c, lo, hi, eps, 3, extra0=(3,)) for c, lo, hi in fr]
tot, comps = run(lines, eps) if lines else (dict(nt=0, single=0, multi=0, work=0, deferred=0, cpu=0.0, wall=0.0), [])
S = [c for c, tag in comps if c[-1] % 3 and c[-2] % 3]
D = [c for c, tag in comps if not (c[-1] % 3 and c[-2] % 3)]
print(f"k={k} eps={eps:+d} part {part}/{nparts}: prefixes {len(fr)}, t treated {tot['nt']}, single {tot['single']}, "
      f"multi {tot['multi']}, multi work {tot['work']}, deferred (factored) {tot['deferred']}, "
      f"completions prime to 3 {len(S)}, completions with 3 | p or q {len(D)}, cpu {tot['cpu']:.1f}s, wall {tot['wall']}s", flush=True)
for c in S: print("   PRIME TO 3", c)
for c in D: print("   3 | p or q", c)
