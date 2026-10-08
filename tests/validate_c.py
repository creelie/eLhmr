#!/usr/bin/env python3
"""The third implementation (lastthree_c.py) as a complete search from depth k - 3, for n + eps = 2 phi(n)
with p_1 >= 5, k = 7..14 and both signs: it must find no solution, and the number of choices of p_{k-2} it
treats must equal the number of nodes at depth k - 2 of the search (last entries of the level profiles in
logs/walls.log).  The routine divisors_sum requires gcd(r, C) = 1, which holds here by the congruence prune."""
import sys, time
sys.path.insert(0, ".")
import lastthree as L, lastthree_c as LC

DEPTH_K2 = {7: 0, 8: 1, 9: 1, 10: 1, 11: 7, 12: 63, 13: 730, 14: 29631}
ok = True
for eps in (-1, 1):
    for k in range(7, 15):
        t0 = time.time(); st = LC.StatsC(); cands = []; ns = 0; sols = []
        for chosen, A, B, lo, hi in L.frontier(k, 5, 2, 1, eps, 3):
            n, s = LC.node_c(tuple(chosen), A, B, lo, hi, 2, 1, eps, stats=st, cands=cands)
            ns += n; sols += s
        good = ns == DEPTH_K2[k] and not sols
        ok &= good
        print(f"eps={eps:+d} k={k:2d}: solutions {sols}; {ns} choices of p_(k-2) (expected {DEPTH_K2[k]}), "
              f"trial divisions {st.direct}, sums tested {st.sums}, integer completions {st.found} "
              f"({time.time()-t0:.0f}s)", flush=True)

# The known solutions are found from their prefixes: for each of the 56 solutions of the validation equations
# 2^k (n - 1) = (2^k + m) phi(n) and each Fermat-type solution of n + 1 = 2 phi(n) with at least three prime
# factors, completions_c applied to (p_1, ..., p_{k-2}) must return exactly that solution among its completions.
import json
from math import prod
known = json.load(open("data/known_solutions.json"))
cases = []
for k, key in ((4, "S4"), (5, "S5")):
    for n, half in known[key]:
        ps = [2 * h + 1 for h in half]; phi = prod(p - 1 for p in ps)
        cases.append((ps, 2 ** k * (n - 1) // phi, 2 ** k, -1))
for ps in ([3, 5, 17], [3, 5, 17, 257], [3, 5, 17, 353, 929], [3, 5, 17, 257, 65537],
           [3, 5, 17, 353, 929, 83623937]):
    cases.append((ps, 2, 1, +1))
found = 0
for ps, a, b, eps in cases:
    pre = tuple(ps[:-2])
    got = LC.completions_c(pre, prod(pre), prod(x - 1 for x in pre), a, b, eps)
    found += any(sol == tuple(ps) for n, sol in got)
print(f"known solutions recovered from their prefixes: {found} of {len(cases)}")
print("all validations passed" if ok and found == len(cases) else "VALIDATION FAILED")
