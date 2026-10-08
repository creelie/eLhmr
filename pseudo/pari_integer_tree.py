#!/usr/bin/env python3
"""Theorem 9.3 (i), second program: all odd integers 5 <= x_1 < ... < x_k, none divisible by 3 (with --with3:
3 <= x_1 < ... < x_k, any odd entries), with
    x_1 ... x_k + eps = 2 (x_1 - 1) ... (x_k - 1).
Bounds derived here from the equation alone: with A, B the products over a prefix, c = 2B - A, and m >= 2 entries
left, the next entry x satisfies c x - 2B >= 1 and x^m A >= 2B (x-1)^m; with 2 entries left, (c p - 2B)(c q - 2B)
= 2AB + eps c with 1 <= c p - 2B <= sqrt(2AB + eps c), solved by factoring with PARI/GP (every factor proved prime).
The gcd conditions are used only as a prune (they follow from the equation).  No code is shared with the rest of the
repository.  Needs gp (PARI/GP) on the PATH.
usage: pari_integer_tree.py k eps [--with3]"""
import sys, subprocess
from math import gcd, prod, isqrt

k, eps = int(sys.argv[1]), int(sys.argv[2]); with3 = '--with3' in sys.argv
PMIN = 3 if with3 else 5
leaves = []
nodes = [0]

def upper(A, B, m, lo):
    def ok(x): return x ** m * A >= 2 * B * (x - 1) ** m
    if not ok(lo): return lo - 1
    h = lo; s = 1
    while ok(h + s): h += s; s *= 2
    while s > 1:
        s //= 2
        if ok(h + s): h += s
    return h

def rec(xs, A, B):
    nodes[0] += 1
    m = k - len(xs); c = 2 * B - A
    if c <= 0: return
    if m == 2:
        leaves.append((xs, A, B)); return
    lo = max(xs[-1] + 1 if xs else PMIN, (2 * B) // c + 1, PMIN)
    hi = upper(A, B, m, lo)
    for x in range(lo | 1, hi + 1, 2):
        if not with3 and x % 3 == 0: continue
        if gcd(x, B) != 1 or gcd(x - 1, A) != 1: continue
        rec(xs + (x,), A * x, B * (x - 1))

rec((), 1, 1)
Ns = [2 * A * B + eps * (2 * B - A) for xs, A, B in leaves]
sols = []
if Ns:
    inp = "\n".join(f"f=factor({N});for(i=1,#f~,if(!isprime(f[i,1]),error(\"np\")));print(concat([#f~],concat(Vec(f[,1]),Vec(f[,2]))));" for N in Ns) + "\nquit\n"
    out = subprocess.run(["gp", "-q", "-s", "512000000"], input=inp, capture_output=True, text=True).stdout.strip().splitlines()
    assert len(out) == len(Ns)
    for (xs, A, B), N, line in zip(leaves, Ns, out):
        v = [int(t) for t in line.strip()[1:-1].split(",")]; n = v[0]
        fac = list(zip(v[1:1 + n], v[1 + n:]))
        assert prod(p ** e for p, e in fac) == N
        c = 2 * B - A
        divs = [1]
        for p, e in fac: divs = [d * p ** i for d in divs for i in range(e + 1)]
        r = isqrt(N)
        for d in divs:
            if d > r or (d + 2 * B) % c or (N // d + 2 * B) % c: continue
            p, q = (d + 2 * B) // c, (N // d + 2 * B) // c
            if p <= xs[-1] or q <= p: continue
            t = xs + (p, q)
            assert prod(t) + eps == 2 * prod(x - 1 for x in t)
            if all(x % 2 for x in t): sols.append(t)
print(f"k={k} eps={eps:+d} with3={with3}: nodes {nodes[0]}, leaves {len(leaves)}, solutions {len(sols)}"
      + (f", s values {sorted(set(sum(1 for x in t if x % 3 == 0) for t in sols))}" if sols else ""), flush=True)
for t in sols: print("   ", t)
