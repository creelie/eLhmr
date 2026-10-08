#!/usr/bin/env python3
"""First-moment count of Section 9.6: the expected number of solutions of  x_1 ... x_k + eps = 2 prod(x_i - 1)  in odd
integers 5 <= x_1 < ... < x_k prime to 3 (with --with3: odd integers 3 <= x_1 < ... < x_k), under the heuristic that
the divisors of N = 2AB + eps c at a node with two entries left fall into the class -2B (mod c) at random.

The tree is enumerated exactly while a node has at most W0 admissible children, and otherwise S children are
importance-sampled (half from the first J admissible ones, half log-uniformly in x - 2B/c).  At a node with two entries
left the expected number of divisors d of N with d = -2B (mod c) and c x_{k-2} - 2B < d <= sqrt(N) is taken as
rho log(sqrt(N) / d_lo) / c, where rho accounts for the prune modulo the small primes of A and B.
The calibration of the paper (entry 3 allowed, eps = -1, k = 4..7):
    first_moment.py 4 -1 --with3 --W0 100000      (exact tree; likewise k = 5, 6)
    first_moment.py 7 -1 --with3 --W0 1000 --reps 20
usage: first_moment.py k eps [--with3] [--W0 n] [--S n] [--J n] [--seed n] [--reps n]"""
import sys, math, random, argparse
from math import gcd, isqrt
import gmpy2
from gmpy2 import mpz

ap = argparse.ArgumentParser()
ap.add_argument('k', type=int); ap.add_argument('eps', type=int)
ap.add_argument('--with3', action='store_true')
ap.add_argument('--W0', type=int, default=64); ap.add_argument('--S', type=int, default=3); ap.add_argument('--J', type=int, default=8)
ap.add_argument('--seed', type=int, default=1); ap.add_argument('--reps', type=int, default=1)
a = ap.parse_args()
PMIN = 3 if a.with3 else 5
SP = [p for p in range(3, 2000) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
k = a.k

def adm(x, A, B):
    if x % 2 == 0 or x < PMIN: return False
    if not a.with3 and x % 3 == 0: return False
    return gcd(x, B) == 1 and gcd(x - 1, A) == 1

def upper(A, B, m, lo):
    def ok(x): return x ** m * A >= 2 * B * (x - 1) ** m
    if not ok(lo): return lo - 1
    h = lo; s = 1
    while ok(h + s): h += s; s *= 2
    while s > 1:
        s //= 2
        if ok(h + s): h += s
    return h

def rho_entry(A, B):
    g = 1.0
    for r in SP:
        if r == 3 and not a.with3: continue
        if B % r == 0: g *= 1 - 1 / r
        if A % r == 0: g *= 1 - 1 / r
    return g

def E2(xl, A, B, c):
    N = 2 * A * B + a.eps * c
    Dlo = max(c * xl - 2 * B, 1); Dhi = isqrt(N)
    if Dhi <= Dlo: return 0.0
    g = rho_entry(A, B)
    return g * g * (1.0 if a.with3 else 2 / 3) * 0.9 * (math.log(Dhi) - math.log(Dlo)) / c

stats = dict(exact_nodes=0, sampled_nodes=0, leaves=0)
def est(xl, A, B, depth):
    m = k - depth
    c = 2 * B - A
    if c <= 0: return 0.0
    if m == 2:
        stats['leaves'] += 1
        return E2(xl, A, B, c)
    lo = max(xl + 1, int(2 * B // c) + 1, PMIN)
    hi = upper(A, B, m, lo)
    if hi < lo: return 0.0
    # collect up to W0+1 admissible children from lo
    kids = []; x = lo
    while x <= hi and len(kids) <= a.W0:
        if adm(x, A, B): kids.append(x)
        x += 1
    if len(kids) <= a.W0 and x > hi:
        stats['exact_nodes'] += 1
        return sum(est(y, A * y, B * (y - 1), depth + 1) for y in kids)
    stats['sampled_nodes'] += 1
    near = kids[:a.J]; far_lo = near[-1] + 1
    xs_f = float(2 * B) / float(c) if B < 10 ** 300 else float(mpz(2 * B) // c)
    L0 = math.log(far_lo - 1 - xs_f); L1 = math.log(hi - xs_f); U = L1 - L0
    tot = 0.0
    for _ in range(a.S):
        if random.random() < 0.5:
            y = random.choice(near); P = 0.5 / len(near)
        else:
            u = random.uniform(L0, L1); y = max(far_lo, math.ceil(xs_f + math.exp(u)))
            while y <= hi and not adm(y, A, B): y += 1
            if y > hi: continue
            yp = y - 1
            while yp >= far_lo and not adm(yp, A, B): yp -= 1
            lower = max(yp, far_lo - 1)
            P = 0.5 * (math.log(y - xs_f) - math.log(lower - xs_f)) / U
            if P <= 0: continue
        tot += est(y, A * y, B * (y - 1), depth + 1) / P
    return tot / a.S

res = []
for r in range(a.reps):
    random.seed(a.seed + r)
    res.append(est(0, mpz(1), mpz(1), 0))
mean = sum(res) / len(res)
sd = (sum((v - mean) ** 2 for v in res) / max(1, len(res) - 1)) ** 0.5 / max(1, len(res)) ** 0.5
print(f"k={k} eps={a.eps:+d} with3={a.with3} W0={a.W0} S={a.S} reps={a.reps}: E ~ {mean:.4g} (+- {sd:.2g})  {stats}", flush=True)
