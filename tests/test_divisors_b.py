#!/usr/bin/env python3
"""The second implementation (lastthree_b.divisors_b) against brute force, as in test_divisors.py but with
t <= sqrt(N) and gcd(r, c) = 1, which is the case that occurs in the search."""
import sys, random, time, math
sys.path.insert(0, ".")
import lastthree_b as LB
from gmpy2 import mpz, next_prime, gcd, isqrt

rng = random.Random(4242)
def rand_prime(bits): return int(next_prime(mpz(rng.getrandbits(bits)) | (1 << (bits - 1))))
bad = 0; cases = 0; nonempty = 0; fact = 0; t0 = time.time(); lg = []; ndig = 0
for trial in range(4000):
    fac = {}
    for _ in range(rng.randint(1, 7)):
        p = rand_prime(rng.choice([2, 3, 5, 8, 12, 16, 20, 25, 30, 40]))
        fac[p] = fac.get(p, 0) + rng.choice([1, 1, 1, 2])
    N = 1; divs = [1]
    for p, e in fac.items():
        N *= p ** e; divs = [d * p ** i for d in divs for i in range(e + 1)]
    cb = max(2, int(N.bit_length() * rng.uniform(0.02, 0.55)))
    c = rng.getrandbits(cb) | 1 | (1 << (cb - 1))
    sN = int(isqrt(N))
    if rng.random() < 0.6:
        cand = [d for d in divs if d <= sN and gcd(d, c) == 1]
        if not cand: continue
        r = rng.choice(cand) % c
    else:
        r = rng.randrange(c)
        if gcd(r, c) != 1: continue
    want = sorted(d for d in divs if d % c == r and d <= sN)
    got = LB.divisors_b(N, c, r, max_boxes=int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
    if got is None:
        got = LB.divisors_by_factoring_b(N, c, r); fact += 1
    got = sorted(int(x) for x in got)
    cases += 1; nonempty += bool(want)
    lg.append(3 * math.log10(c) - math.log10(N)); ndig = max(ndig, len(str(N)))
    if got != want:
        bad += 1; print("MISMATCH", N, c, r, want, got)
        if bad > 5: break
print(f"{cases} cases ({nonempty} with divisors in the class, {fact} factored), N up to {ndig} digits, "
      f"log10(c^3/N) from {min(lg):.1f} to {max(lg):.1f}, mismatches: {bad}, "
      f"{time.time()-t0:.1f}s")
