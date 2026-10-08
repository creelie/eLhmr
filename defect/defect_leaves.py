"""Proposition 9.14: every l-set of size k - 1 for l (see defect_bound.py), with Lehmer's equation decided
exactly for each.  Prints the number of l-sets, how many have l | C, how many also have C | A - 1, and the
solutions (there are none).  usage: python3 defect/defect_leaves.py l k [cap]"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from defect_bound import search

l, k = int(sys.argv[1]), int(sys.argv[2])
cap = int(sys.argv[3]) if len(sys.argv) > 3 else None
t0 = time.time()
try:
    first, st = search(l, k - 1, all_sets=True, cap=cap)
except RuntimeError as e:
    print(f"l = {l}, k = {k}: stopped: {e} ({time.time() - t0:.0f}s)")
    sys.exit(1)
print(f"l = {l}, k = {k}: sets S {st['sets']}{' (cap reached)' if st['capped'] else ''}, with l | C {st['div_l']}, "
      f"with C | A-1 {st['div_A']}, Lehmer numbers {st['solutions']} ({st['nodes']} nodes, {time.time() - t0:.1f}s)")
