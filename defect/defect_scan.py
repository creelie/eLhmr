"""k_l of Proposition 9.13 for every prime l in a range (see defect_bound.py).
usage: python3 defect/defect_scan.py lo hi Kmax [margin]"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import primerange
from defect_bound import least_k

lo, hi, Kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
margin = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-9
for l in primerange(lo, hi + 1):
    t0 = time.time()
    k, w = least_k(l, Kmax, margin)
    print(f"l = {l}: k_l = {k if k else '>' + str(Kmax + 1)}"
          + (f", witness ends {w[-4:]}" if w else "") + f" ({time.time() - t0:.1f}s)", flush=True)
