#!/usr/bin/env python3
"""The tree of integer_tree.py restricted to pairwise coprime entries: odd x_1 < x_2 < ... prime to 3 with
gcd(x_i, x_j) = 1 for i != j and gcd(x_i, x_j - 1) = 1, prod x_i/(x_i - 1) < 2, and the exact interval of
Propositions 3.1 and 3.2 (lastthree.interval) for the next entry when k entries are wanted in all.

The tree is traversed down to depth k - 3.  Every prefix of length 5 or more with defect c = 2B - A > 0 and
c x_j < 2B, which one more entry can complete, is collected with its defect; these are the seeds of descent_coprime.py.
Writes coprime_prefixes_k<k>.pkl and prints, for each length, the number of these prefixes, the sum of 1/c and the
smallest defect.

usage: coprime_tree.py k [eps]      (eps = -1 by default; the intervals for eps = +1 differ only slightly)"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import lastthree as L
from sympy import primefactors


def tree(k, eps):
    pre = {}; nodes = [0]

    def rec(xs, A, B, R0, R1):
        nodes[0] += 1
        j = len(xs); m = k - j
        c = 2 * B - A
        if c <= 0: return
        if j >= 5 and 2 * B > c * xs[-1]: pre[tuple(xs)] = c
        if m <= 3: return
        pj = xs[-1] if xs else 1
        lo, hi = L.interval(A, B, pj, m, 2, 1, eps)
        lo = max(lo, pj + 1, 5)
        x = lo | 1
        while x <= hi:
            # R0: odd primes of the earlier x_i - 1 (x must avoid 0); R1: primes of the earlier x_i (x must avoid 0 and 1)
            if x % 3 and all(x % r for r in R0) and all(x % r not in (0, 1) for r in R1):
                f0 = [r for r in primefactors(x - 1) if r > 2 and r not in R0]
                rec(xs + (x,), A * x, B * (x - 1), R0 + tuple(f0), R1 + tuple(primefactors(x)))
            x += 2

    rec((), 1, 1, (), ())
    return pre, nodes[0]


def main():
    k = int(sys.argv[1]); eps = int(sys.argv[2]) if len(sys.argv) > 2 else -1
    t0 = time.time()
    pre, visited = tree(k, eps)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"coprime_prefixes_k{k}.pkl")
    pickle.dump(pre, open(out, "wb"))
    print(f"k={k} eps={eps:+d}: {visited} nodes visited, {len(pre)} prefixes with 0 < c x_j < 2B, "
          f"sum of 1/c {sum(1.0 / c for c in pre.values()):.3e}  ({time.time() - t0:.0f}s)")
    by = {}
    for p, c in pre.items():
        b = by.setdefault(len(p), [0, 0.0, None]); b[0] += 1; b[1] += 1.0 / c
        if b[2] is None or c < b[2][0]: b[2] = (c, p)
    for d in sorted(by):
        print(f"  length {d}: {by[d][0]} prefixes, sum of 1/c {by[d][1]:.3e}, smallest defect {by[d][2][0]} at {by[d][2][1]}")


if __name__ == "__main__":
    main()
