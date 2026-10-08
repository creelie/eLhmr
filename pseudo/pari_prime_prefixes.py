#!/usr/bin/env python3
"""Theorem 9.3 (ii), second program: an independent check of the entries below the prime prefixes.

For each prime prefix x_1 < ... < x_j (j = k-3, p_1 >= 5; with --with3, p_1 >= 3) of the search of Theorems 1.1 and
1.4 (lastthree.frontier), every odd t with 3 not dividing t (any t with --with3) and
    t > x_j,  c t - 2B >= 1,  t^3 A >= 2B (t-1)^3
(these follow from the equation for x_j < t < p < q, and do not use the paper's interval)
and gcd(t, x_i - 1) = gcd(x_i, t - 1) = 1, we FACTOR  N = 2 A_t B_t + eps c_t  completely with PARI/GP, prove every
prime factor prime, and list every divisor d <= sqrt(N) with d = -2B_t (mod c_t); p = (d + 2B_t)/c_t,
q = (N/d + 2B_t)/c_t.  Every integer solution (t, p, q), t < p <= q, of  A t p q + eps = 2B (t-1)(p-1)(q-1)  is
reported, whether or not p, q are odd, prime to 3 or admissible, and then classified: "admissible" means odd,
p < q and gcd(x_i, x_j - 1) = 1 for all entries, and "3-free" means that 3 divides neither p nor q.  Apart from the list of
prefixes no code is shared with tail3 or lastthree.  Needs gp (PARI/GP) on the PATH.
usage: pari_prime_prefixes.py k eps [--with3] [--sample n seed]"""
import sys, subprocess, random, math, os
from math import gcd, prod, isqrt

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lastthree import frontier
k, eps = int(sys.argv[1]), int(sys.argv[2]); with3 = '--with3' in sys.argv
samp, seed = 0, 1
if '--sample' in sys.argv:
    i = sys.argv.index('--sample'); samp, seed = int(sys.argv[i + 1]), int(sys.argv[i + 2])
fr = [[list(map(int, c)), int(lo), int(hi)] for c, A, B, lo, hi in frontier(k, 3 if with3 else 5, 2, 1, eps, 3)]

def trange(xs):
    A = prod(xs); B = prod(x - 1 for x in xs); c = 2 * B - A
    lo = max(xs[-1] + 1 if xs else (3 if with3 else 5), (2 * B) // c + 1)
    # largest t with t^3 A >= 2B (t-1)^3
    hi = lo
    if hi ** 3 * A < 2 * B * (hi - 1) ** 3: return A, B, c, lo, lo - 1
    step = 1
    while (hi + step) ** 3 * A >= 2 * B * (hi + step - 1) ** 3: hi += step; step *= 2
    while step > 1:
        step //= 2
        if (hi + step) ** 3 * A >= 2 * B * (hi + step - 1) ** 3: hi += step
    return A, B, c, lo, hi

tasks = []
for xs, _, _ in fr:
    A, B, c, lo, hi = trange(xs)
    for t in range(lo | 1, hi + 1, 2):
        if t % 3 == 0 and not with3: continue
        if any(gcd(t, x - 1) != 1 or gcd(x, t - 1) != 1 for x in xs): continue
        tasks.append((xs, t))
ntot = len(tasks)
if samp and samp < ntot:
    random.seed(seed); tasks = random.sample(tasks, samp)
Ns = []
for xs, t in tasks:
    A = prod(xs) * t; B = prod(x - 1 for x in xs) * (t - 1); c = 2 * B - A
    assert c >= 1
    Ns.append(2 * A * B + eps * c)
# factor with PARI in one batch
inp = "\n".join(f"f=factor({N});for(i=1,#f~,if(!isprime(f[i,1]),error(\"not proved prime\")));print(concat([#f~],concat(Vec(f[,1]),Vec(f[,2]))));" for N in Ns) + "\nquit\n"
out = subprocess.run(["gp", "-q", "-s", "512000000"], input=inp, capture_output=True, text=True).stdout.strip().splitlines()
assert len(out) == len(Ns), (len(out), len(Ns))
def parse(s):
    v = [int(x) for x in s.strip()[1:-1].split(",")]
    n = v[0]
    return list(zip(v[1:1 + n], v[1 + n:1 + 2 * n]))
found = []
for (xs, t), N, s in zip(tasks, Ns, out):
    fac = parse(s)
    assert prod(p ** e for p, e in fac) == N
    A = prod(xs) * t; B = prod(x - 1 for x in xs) * (t - 1); c = 2 * B - A
    divs = [1]
    for p, e in fac: divs = [d * p ** i for d in divs for i in range(e + 1)]
    r = isqrt(N)
    for d in divs:
        if d > r or (d + 2 * B) % c: continue
        e_ = N // d
        if (e_ + 2 * B) % c: continue
        p, q = (d + 2 * B) // c, (e_ + 2 * B) // c
        if p <= t: continue
        tup = tuple(xs) + (t, p, q)
        assert prod(tup) + eps == 2 * prod(x - 1 for x in tup)
        adm = all(x % 2 and gcd(x, y - 1) == 1 for x in tup for y in tup) and p < q
        free3 = p % 3 and q % 3
        found.append((tup, adm, bool(free3)))
print(f"k={k} eps={eps:+d} with3={with3}: prefixes {len(fr)}, admissible t {ntot}, checked {len(tasks)}, integer solutions {len(found)}, "
      f"admissible {sum(1 for f in found if f[1])}, admissible and 3-free {sum(1 for f in found if f[1] and f[2])}", flush=True)
for f in found: print("   ", f)
