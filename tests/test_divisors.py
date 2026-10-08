#!/usr/bin/env python3
"""divisors_in_class against brute force: random N with known factorisation, random moduli and classes,
including classes that are known to contain divisors.  The modulus c has 2 to 55 per cent of the bits of N, so
that c^3/N ranges over many orders of magnitude on both sides of 1; the range is printed at the end."""
import sys, random, math, time
sys.path.insert(0, ".")
import lastthree as L
from gmpy2 import mpz, next_prime, gcd, isqrt

rng = random.Random(20260930)
def rand_prime(bits): return int(next_prime(mpz(rng.getrandbits(bits)) | (1 << (bits - 1))))
def all_divs(fac):
    ds = [1]
    for p, e in fac: ds = [d * p ** i for d in ds for i in range(e + 1)]
    return ds

bad = 0; cases = 0; nonempty = 0; fact = 0; t0 = time.time(); lg = []; ndig = 0
for trial in range(4000):
    nf = rng.randint(1, 7)
    fac = {}
    for _ in range(nf):
        p = rand_prime(rng.choice([2, 3, 5, 8, 12, 16, 20, 25, 30, 40]))
        fac[p] = fac.get(p, 0) + rng.choice([1, 1, 1, 2])
    fac = list(fac.items())
    N = 1
    for p, e in fac: N *= p ** e
    divs = all_divs(fac)
    nbits = N.bit_length()
    cb = max(2, int(nbits * rng.uniform(0.02, 0.55)))
    c = rng.getrandbits(cb) | 1 | (1 << (cb - 1))
    tmax = rng.choice([isqrt(N), N, rng.randint(1, N)])
    if rng.random() < 0.6:
        cand = [d for d in divs if d <= tmax and gcd(d, c) == 1]
        if not cand: continue
        r = rng.choice(cand) % c
    else:
        r = rng.randrange(c)
    want = sorted(d for d in divs if d % c == r and d <= tmax and d >= 1)
    tt = time.time(); st = L.Stats()
    got = L.divisors_in_class(N, c, r, tmax, stats=st, kappa=rng.choice([0.25, 1.0, 4.0]), max_boxes=50000)
    if time.time() - tt > 1: print("slow", trial, nbits, cb, st.boxes, st.hits, st.direct, flush=True)
    if got is None:
        got = L.divisors_by_factoring(N, c, r, tmax); fact += 1
    got = sorted(int(x) for x in got)
    cases += 1; nonempty += bool(want)
    lg.append(3 * math.log10(c) - math.log10(N)); ndig = max(ndig, len(str(N)))
    if got != want:
        bad += 1
        print("MISMATCH", N, c, r, tmax, want, got)
        if bad > 5: break
print(f"{cases} cases ({nonempty} with divisors in the class, {fact} factored), N up to {ndig} digits, "
      f"log10(c^3/N) from {min(lg):.1f} to {max(lg):.1f}, mismatches: {bad}, {time.time()-t0:.1f}s")
