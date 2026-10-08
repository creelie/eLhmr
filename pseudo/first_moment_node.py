#!/usr/bin/env python3
"""First-moment count of Section 9.6 below one node, for solutions prime to 3 of Lehmer's product equation
(eps = -1), with the heuristic of first_moment.py.  For m = 3, 4, 5 entries left below the prefix
(5, 7, 13, 17, 19, 23, 25, 37, 119), which has the smallest C_9 = 2B - A among the prefixes of length nine, the
last level is summed exactly over the first T0 admissible t and by quadrature beyond, and each level above over the
first X0 admissible x and by S log-uniform samples beyond.  With --tree it also sums the case m = 3 over all 489 nodes
at depth 9 of the tree for k = 12 (integer_tree.py).
usage: first_moment_node.py T0 X0 S [--tree]        (the paper: 1000 30 30 --tree)"""
import math, random, sys
from math import gcd, isqrt, log
random.seed(3)
SP = [p for p in range(5, 2000) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
T0, X0, S = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
TREE = '--tree' in sys.argv
eps = -1
def adm(x, A, B): return x % 2 == 1 and x % 3 != 0 and gcd(x, B) == 1 and gcd(x - 1, A) == 1
def upper(A, B, m, lo):
    def ok(x): return x ** m * A >= 2 * B * (x - 1) ** m
    if not ok(lo): return lo - 1
    h = lo; s = 1
    while ok(h + s): h += s; s *= 2
    while s > 1:
        s //= 2
        if ok(h + s): h += s
    return h
def g2(A, B):
    g = 1.0
    for r in SP:
        if B % r == 0: g *= 1 - 1 / r
        if A % r == 0: g *= 1 - 1 / r
    return g * g * (2 / 3) * 0.9
def E2(xl, A, B):
    c = 2 * B - A; N = 2 * A * B + eps * c
    Dlo = max(c * xl - 2 * B, 1); Dhi = isqrt(N)
    if Dhi <= Dlo: return 0.0
    return g2(A, B) * (log(Dhi) - log(Dlo)) / c
def lnf(z): return math.log(z) if z < 10 ** 300 else z.bit_length() * math.log(2)
def E3(xl, A, B):
    c = 2 * B - A
    if c <= 0: return 0.0
    lo = max(xl + 1, 2 * B // c + 1); hi = upper(A, B, 3, lo)
    if hi < lo: return 0.0
    tot = 0.0; cnt = 0; t = lo
    while t <= hi and cnt < T0:
        if adm(t, A, B): tot += E2(t, A * t, B * (t - 1)); cnt += 1
        t += 1
    if t > hi: return tot
    rho = cnt / (t - lo)
    # quadrature over (t, hi]: E2(u) ~ g2 * L(u) / (c u - 2B), sample 60 log-spaced points in (u - x*)
    xs = 2 * B / c if B < 10 ** 300 else float(2 * B // c)
    a = log(t - xs); b = log(hi - xs); n = 60; acc = 0.0
    for i in range(n):
        u = a + (b - a) * (i + 0.5) / n
        y = int(xs + math.exp(u))
        while not adm(y, A, B): y += 1
        val = E2(y, A * y, B * (y - 1)) * (y - xs)   # integrand in d(log(y - x*)) : f(y) dy = f(y) (y - x*) du
        acc += val * (b - a) / n
    return tot + rho * acc
def Em(m, xl, A, B):
    if m == 3: return E3(xl, A, B)
    c = 2 * B - A
    if c <= 0: return 0.0
    lo = max(xl + 1, 2 * B // c + 1); hi = upper(A, B, m, lo)
    if hi < lo: return 0.0
    tot = 0.0; cnt = 0; x = lo; near = []
    while x <= hi and cnt < X0:
        if adm(x, A, B): tot += Em(m - 1, x, A * x, B * (x - 1)); cnt += 1
        x += 1
    if x > hi: return tot
    rho = cnt / (x - lo)
    xs = 2 * B / c
    a = log(x - xs); b = log(hi - xs); acc = 0.0
    for i in range(S):
        u = random.uniform(a, b); y = int(xs + math.exp(u))
        while not adm(y, A, B): y += 1
        if y > hi: continue
        acc += Em(m - 1, y, A * y, B * (y - 1)) * (y - xs) * (b - a) / S
    return tot + rho * acc
Q = (5, 7, 13, 17, 19, 23, 25, 37, 119)
A = math.prod(Q); B = math.prod(x - 1 for x in Q)
import time
if TREE:
    from integer_tree import depth_k3_nodes
    nodes, _ = depth_k3_nodes(12, eps)
    Es = sorted(((E3(xs[-1], math.prod(xs), math.prod(x - 1 for x in xs)), xs) for xs, lo, hi in nodes), reverse=True)
    print(f"k=12: {len(nodes)} nodes at depth 9, total E ~ {sum(e for e, xs in Es):.3g}; largest "
          + ", ".join(f"{e:.2g} below {tuple(xs[-3:])}" for e, xs in Es[:3]), flush=True)
for m in (3, 4, 5):
    t0 = time.time()
    print(f"node {Q} c={2*B-A}: m={m} (k={len(Q)+m}) E ~ {Em(m, Q[-1], A, B):.3g}  [{time.time()-t0:.0f}s]", flush=True)
