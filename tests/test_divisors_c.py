#!/usr/bin/env python3
"""lastthree_c.divisors_sum against brute force.  The routine assumes gcd(r, c) = 1 and N = r^2 (mod c), which
is the situation of the search.  Two kinds of instance: N = t t* with t = t* = r (mod c) planted (t and t*
factored by FLINT, so that all divisors of N are known), and N = r^2 + c j at random (factored by FLINT).
The ratio c^3/N ranges from about 10^-13 to 10^28."""
import sys, random, time, math
sys.path.insert(0, ".")
import lastthree_c as LC
import flint
from gmpy2 import mpz, gcd, isqrt

rng = random.Random(31415)
def factor(n):
    return [(int(p), int(e)) for p, e in flint.fmpz(int(n)).factor()]
def divisors(fac):
    ds = [1]
    for p, e in fac: ds = [d * p ** i for d in ds for i in range(e + 1)]
    return ds
def merge(f1, f2):
    d = {}
    for p, e in f1 + f2: d[p] = d.get(p, 0) + e
    return list(d.items())

bad = 0; cases = 0; nonempty = 0; planted = 0; t0 = time.time(); lo = hi = 0.0
for trial in range(5000):
    nbits = rng.randint(8, 150)
    # c^3/N from about 2^-40 (the cost of the routine is about 2 (N/c^3)^(1/2)) up to 2^(0.8 nbits)
    cb = max(2, rng.randint(max(2, (nbits - 40) // 3 + 1), max(2, int(0.6 * nbits))))
    c = rng.getrandbits(cb) | (1 << (cb - 1))
    if c < 2: continue
    r = rng.randrange(1, c)
    if gcd(r, c) != 1: continue
    if rng.random() < 0.5:
        # planted: t = r + c u, t* = r + c v with t <= t*, N about 2^nbits
        umax = max(0, (isqrt(mpz(2) ** nbits) - r) // c)
        u = rng.randint(0, int(umax)) if rng.random() < 0.5 else int(math.exp(rng.uniform(0, math.log(int(umax) + 1)))) - 1
        t = r + c * u
        v = max(u, ((mpz(2) ** nbits) // t - r) // c + rng.randint(-2, 2))
        ts = r + c * v
        N = t * ts; fac = merge(factor(t), factor(ts)); planted += 1
    else:
        N = r * r + c * rng.randint(1, max(1, (1 << nbits) // c))
        fac = factor(N)
    N = int(N)
    sN = int(isqrt(N))
    want = sorted(d for d in divisors(fac) if d % c == r and d <= sN)
    got = [int(x) for x in LC.divisors_sum(N, c, r)]
    cases += 1; nonempty += bool(want)
    x = 3 * math.log10(c) - math.log10(N); lo = min(lo, x); hi = max(hi, x)
    if got != want:
        bad += 1; print("MISMATCH", N, c, r, want, got, flush=True)
        if bad > 5: break
print(f"{cases} cases ({planted} planted, {nonempty} with divisors in the class), log10(c^3/N) from {lo:.1f} "
      f"to {hi:.1f}, mismatches: {bad}, {time.time()-t0:.1f}s")
