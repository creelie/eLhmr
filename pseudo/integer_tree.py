#!/usr/bin/env python3
"""Theorem 9.3 (i), first program: no odd integers 5 <= x_1 < ... < x_k, none divisible by 3, prime or not, satisfy
    x_1 ... x_k + eps = 2 (x_1 - 1) ... (x_k - 1)
for 3 <= k <= KMAX (default 12), for eps = -1 and eps = +1.

The tree is that of the paper's search with integer entries: odd x, 3 not dividing x, x != 0 mod r for the odd primes
r of the earlier x_i - 1 and x != 1 mod r for the primes r of the earlier x_i (these follow from the equation, since a
common divisor of x_i and x_j - 1 divides eps), prod x_i/(x_i - 1) < 2, and the exact interval of Propositions 3.1 and
3.2 (lastthree.interval), whose proof uses only the equation with phi(n) replaced by prod(x_i - 1).  At depth k - 3
every admissible t = x_{k-2} of the interval is passed to tail3 (mode 3), which finds all integer completions (t, p, q).
usage: integer_tree.py [KMAX]"""
import sys, os, time
from tail3lib import L, line_for, run
from sympy import factorint

def small_factors(x):
    return list(factorint(int(x)).keys())

def children(lo, hi, R0, R1):
    x = lo | 1
    while x <= hi:
        if x % 3 and all(x % r for r in R0) and all(x % r != 1 for r in R1):
            yield x
        x += 2

def depth_k3_nodes(k, eps):
    out = []; nodes = [0]
    def rec(xs, A, B, R0, R1):
        nodes[0] += 1
        j = len(xs); m = k - j
        if A >= 2 * B: return
        pj = xs[-1] if xs else 1
        lo, hi = L.interval(A, B, pj, m, 2, 1, eps)
        lo = max(lo, pj + 1, 5)
        if hi < lo: return
        if m == 3:
            out.append((list(xs), lo, hi)); return
        for x in children(lo, hi, R0, R1):
            f0 = [r for r in small_factors(x - 1) if r > 2 and r not in R0]
            f1 = [r for r in small_factors(x) if r not in R1]
            rec(xs + (x,), A * x, B * (x - 1), R0 + tuple(f0), R1 + tuple(f1))
    rec((), 1, 1, (), ())
    return out, nodes[0]

def main():
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for eps in (-1, 1):
        for k in range(3, KMAX + 1):
            t0 = time.time()
            nodes, visited = depth_k3_nodes(k, eps)
            lines = [line_for(x, lo, hi, eps, 3, extra0=(3,)) for x, lo, hi in nodes]
            tot, comps = run(lines, eps) if lines else (dict(nt=0, deferred=0, cpu=0.0), [])
            S = [c for c, tag in comps if c[-1] % 3 and c[-2] % 3]
            print(f"k={k} eps={eps:+d}: {visited} nodes visited, {len(nodes)} nodes at depth {k-3}, "
                  f"t treated {tot['nt']}, deferred (factored) {tot['deferred']}, completions prime to 3 {len(S)}, "
                  f"completions with 3 | p or q {len(comps) - len(S)}, {time.time() - t0:.1f}s", flush=True)
            for c in comps: print("   COMPLETION", c)

if __name__ == "__main__":
    main()
