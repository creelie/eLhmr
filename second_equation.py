#!/usr/bin/env python3
"""Theorems 1.3 and 1.4 for n + 1 = 2 phi(n).
Part 1 (Theorem 1.3): p_1 >= 3, 2 <= k <= 7.  Program 1 with divisor enumeration; every integer factored has
fewer than 25 digits, so every factorisation is certified (deterministic primality below 3.3e24).
Program 2 (enumeration only) is also run for k <= 6 and must agree node for node.
Part 2 (Theorem 1.4): p_1 >= 5, 7 <= k <= 14, both programs; nothing may be found and node counts must agree.
Runtime: a few minutes on one core."""
import sys, time
sys.path.insert(0, ".")
from tree_search import Search
from tree_enum import run
known = {2: [15], 3: [255], 4: [65535], 5: [83623935, 4294967295], 6: [6992962672132095], 7: []}
for k in range(2, 8):
    t0 = time.time(); S = Search(k, 2, 1, pmin=3, eps=+1, enum_limit=10**6, factor_digits=34); S.run()
    sols = sorted(n for n, _ in S.sols); line = ""
    if k <= 6:
        n2, l2, mr2, s2 = run(k, pmin=3, a=2, b=1, eps=+1)
        assert n2 == S.nodes and sorted(n for n, _ in s2) == sols
        line = f" | program 2 nodes={n2} solutions={sorted(n for n, _ in s2)}"
    print(f"Part 1  k={k}: nodes={S.nodes:5d} leaves={S.leaves:5d} maxwidth={S.max_range} maxDdigits={getattr(S, 'max_D', 0)} "
          f"solutions={sols} ({time.time()-t0:.1f}s){line}", flush=True)
    assert sols == known[k] and getattr(S, "max_D", 0) <= 24
for k in range(7, 15):
    t0 = time.time(); S = Search(k, 2, 1, pmin=5, eps=+1, enum_limit=10**6, factor_digits=34); S.run(); t1 = time.time()
    n2, l2, mr2, s2 = run(k, pmin=5, a=2, b=1, eps=+1); t2 = time.time()
    print(f"Part 2  k={k:2d}: program 1 nodes={S.nodes:6d} sols={S.sols} ({t1-t0:.1f}s) | program 2 nodes={n2:6d} "
          f"leaves={l2} maxwidth={mr2} sols={s2} ({t2-t1:.1f}s)", flush=True)
    assert S.nodes == n2 and not S.sols and not s2
print("Theorem 1.3: the solutions with omega(n) <= 7 are exactly the known ones.  "
      "Theorem 1.4: no solution with 3 not dividing n and omega(n) <= 14.")
