"""Independent check by a totient sieve up to N: no composite n <= N with phi(n) | n-1; the n <= N with
phi(n) | n+1 are 1, 2, 3, 15, 255, 65535, 83623935; and the solutions n <= N of
2^k (n-1) = (2^k+m) phi(n) with omega(n) = k in {4,5}, n odd squarefree, are exactly those in known_solutions.json."""
import sys, json, time
import numpy as np
from sympy import primerange
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**8
t0 = time.time()
phi = np.arange(N + 1, dtype=np.int64); om = np.zeros(N + 1, dtype=np.int8); sqf = np.ones(N + 1, dtype=bool)
for p in primerange(2, N + 1):
    phi[p::p] -= phi[p::p] // p; om[p::p] += 1
    if p * p <= N: sqf[p*p::p*p] = False
n = np.arange(N + 1, dtype=np.int64)
lehmer = np.nonzero((n[2:] - 1) % phi[2:] == 0)[0] + 2
print("phi(n) | n-1, 2 <= n <= N, composite:", [int(x) for x in lehmer if om[x] > 1 or not sqf[x]])
print("phi(n) | n+1, 1 <= n <= N:", [int(x) for x in np.nonzero((n[1:] + 1) % phi[1:] == 0)[0] + 1])
known = json.load(open("data/known_solutions.json"))
for k, key, mmax in ((4, "S4", 40), (5, "S5", 85)):
    sel = (om == k) & sqf & (n % 2 == 1)
    idx = np.nonzero(sel)[0]
    num = (2**k) * (idx - 1); ph = phi[idx]
    ok = (num % ph == 0)
    idx, q = idx[ok], num[ok] // ph[ok]
    found = sorted(int(x) for x, qq in zip(idx, q) if 1 <= qq - 2**k <= mmax)
    kn = sorted(x for x, _ in known[key] if x <= N)
    print(f"k={k}: sieve finds {len(found)} solutions <= N; known list has {len(kn)} <= N; identical: {found == kn}")
print(f"N = {N:.0e}, time {time.time()-t0:.0f}s")
