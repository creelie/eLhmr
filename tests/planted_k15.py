#!/usr/bin/env python3
"""Planted divisors at the scale of the k = 15 search, for all three implementations.

For sampled pairs (prefix, s) of the search, with c = C', r = -2B' mod c and N = 2A'B' - c as in the search,
N is replaced by N* = t t* with t = r + c u (u log-uniform in [0, U]) and t* = r + c v, v chosen so that N* is
close to N and t <= t*.  Every implementation must return t among the divisors of N* in the class r mod c
below sqrt(N*), and everything it returns must be such a divisor.

The sum route (lastthree_c) is run on every instance.  The lattice routes are run with factoring switched
off and a limit of 20000 boxes (they return None beyond it) and a time limit of TLIM seconds per instance:
a planted divisor puts a whole line of the coset v = alpha - u (mod c) into the box that contains it, and the
lattice routes examine every point of that line inside the box, which for large u can take minutes.  In the
search itself no such line is present unless a divisor is, so this does not affect the runs.
Uses 4 processes."""
import sys, json, random, math, time, signal, multiprocessing as mp
sys.path.insert(0, ".")
import lastthree as L, lastthree_b as LB, lastthree_c as LC
from gmpy2 import mpz, isqrt

TLIM = 5

class Timeout(Exception): pass
def _alarm(sig, frame): raise Timeout()

def run_limited(f):
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(TLIM)
    try:
        return f()
    except Timeout:
        return "timeout"
    finally:
        signal.alarm(0)

def one(args):
    chosen, s, seed = args
    rng = random.Random(seed)
    A = 1; B = 1
    for p in tuple(chosen) + (s,): A *= p; B *= p - 1
    A = mpz(A); B = mpz(B); c = 2 * B - A; N = 2 * A * B - c; r = (-2 * B) % c
    U = (isqrt(N) - r) // c
    u = max(mpz(0), min(U, mpz(int(math.exp(rng.uniform(0, math.log(float(U) + 1))))) - 1))
    t = r + c * u
    v = max(u, (N // t - r) // c + rng.randint(-3, 3))
    Ns = t * (r + c * v); sN = isqrt(Ns)
    res = {"x": 3 * math.log10(c) - math.log10(N), "uU": float(u) / float(U) if U else 0.0}
    got = {"C": LC.divisors_sum(Ns, c, r),
           "A": run_limited(lambda: L.divisors_in_class(Ns, c, r, sN, max_boxes=20000)),
           "B": run_limited(lambda: LB.divisors_b(Ns, c, r, max_boxes=20000))}
    for name, g in got.items():
        if g is None or g == "timeout":
            res[name] = "limit" if g is None else "timeout"; continue
        g = sorted(int(x) for x in g)
        res[name] = "ok" if int(t) in g and all(Ns % x == 0 and x % c == r and x <= sN for x in g) else "FAIL"
        got[name] = g
    done = [g for g in got.values() if isinstance(g, list)]
    res["agree"] = all(g == done[0] for g in done)
    return res

if __name__ == "__main__":
    rng = random.Random(15)
    fr = json.load(open("data/k15/frontier.json"))
    order = sorted(range(len(fr)), key=lambda i: -(fr[i][2] - fr[i][1]))
    samples = []
    for i in order[:40]:                       # just above the lower end of the 40 longest intervals
        c_, lo, hi = fr[i]
        ss = L.primes_in(lo, min(hi, lo + 200000)); ss = ss[L.admissible_mask(ss, tuple(c_))]
        samples += [(c_, int(s)) for s in rng.sample(list(ss), min(10, len(ss)))]
    while len(samples) < 1400:                 # anywhere
        i = rng.randrange(len(fr)); c_, lo, hi = fr[i]
        ss = L.primes_in(lo, min(hi, lo + rng.choice([10**3, 10**5, 10**7]))); ss = ss[L.admissible_mask(ss, tuple(c_))]
        if len(ss): samples.append((c_, int(rng.choice(list(ss)))))
    jobs = [(c_, s, 1000 + j) for j, (c_, s) in enumerate(samples)]
    t0 = time.time(); out = []
    with mp.Pool(4) as pool:
        for j, res in enumerate(pool.imap(one, jobs, chunksize=4)):
            out.append(res)
            if (j + 1) % 200 == 0: print(f"{j+1}/{len(jobs)} ({time.time()-t0:.0f}s)", flush=True)
    xs = [r["x"] for r in out]
    print(f"{len(out)} planted instances, log10(c^3/N) from {min(xs):.1f} to {max(xs):.1f}")
    for name in "CAB":
        cnt = {k: sum(r[name] == k for r in out) for k in ("ok", "FAIL", "limit", "timeout")}
        print(f"  {name}: planted divisor found {cnt['ok']}, wrong or missing {cnt['FAIL']}, "
              f"box limit {cnt['limit']}, time limit {cnt['timeout']}")
    slow = [r["uU"] for r in out if r["A"] == "timeout" or r["B"] == "timeout"]
    if slow: print(f"  instances stopped by the time limit have u/U from {min(slow):.2g} to {max(slow):.2g}")
    dis = sum(not r["agree"] for r in out)
    bad = sum(r[n] == "FAIL" for r in out for n in "CAB")
    print(f"disagreements between completed runs: {dis}; failures: {bad}; {time.time()-t0:.0f}s")
    print("planted test passed" if dis == 0 and bad == 0 and all(r["C"] == "ok" for r in out) else "PLANTED TEST FAILED")
