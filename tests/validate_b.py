#!/usr/bin/env python3
"""The same validations as validate_lastthree.py, for the second implementation (lastthree_b.py)."""
import json, sys, time
sys.path.insert(0, ".")
import lastthree_b as LB

def search(k, pmin, a, b, eps):
    st = LB.StatsB(); sols = []; ns = 0
    for chosen, A, B, lo, hi in LB.frontier_rational(k, pmin, a, b, eps, 3):
        n_s, s_ = LB.node_b(chosen, A, B, lo, hi, a, b, eps, stats=st)
        ns += n_s; sols += s_
    return sols, ns, st

known = json.load(open("data/known_solutions.json"))
for k, key, mmax in ((4, "S4", 40), (5, "S5", 85)):
    kn = {n for n, _ in known[key]}
    t0 = time.time(); found = set(); NS = 0; F = 0
    for m in range(1, mmax + 1):
        sols, ns, st = search(k, 3, 2 ** k + m, 2 ** k, -1)
        found |= {n for n, _ in sols}; NS += ns; F += st.factored
    print(f"(1) k={k}: {len(found)} solutions, equal to the list: {found == kn}; "
          f"{NS} choices of p_(k-2), {F} factored  ({time.time()-t0:.0f}s)", flush=True)
    assert found == kn
expect = {3: {255}, 4: {65535}, 5: {83623935, 4294967295}, 6: {6992962672132095}, 7: set()}
for k in range(3, 8):
    t0 = time.time(); sols, ns, st = search(k, 3, 2, 1, +1); got = {n for n, _ in sols}
    print(f"(2) k={k}: {sorted(got)}; {ns} choices of p_(k-2), boxes {st.boxes}, factored {st.factored}  "
          f"({time.time()-t0:.0f}s)", flush=True)
    assert got == expect[k]
for eps in (-1, +1):
    for k in range(7, 15):
        t0 = time.time(); sols, ns, st = search(k, 5, 2, 1, eps)
        print(f"(3) eps={eps:+d} k={k:2d}: solutions {sols}; {ns} choices of p_(k-2), boxes {st.boxes}, "
              f"lattice points {st.points}, factored {st.factored}  ({time.time()-t0:.0f}s)", flush=True)
        assert sols == []
print("all validations passed")
