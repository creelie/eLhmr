#!/usr/bin/env python3
"""Theorem 1.1: no n = p_1 ... p_k with 5 <= p_1 < ... < p_k, k <= 14, satisfies n - 1 = 2 phi(n).
By Lemmas 2.2 and 2.3 of the paper this is all that is needed for omega(n) >= 15 whenever
phi(n) | n - 1 and n is composite.  Program 2 (enumeration only) is the proof; Program 1 corroborates it,
and the two node counts must agree at every k.  Runtime: about 10 minutes on one core."""
import sys, time
sys.path.insert(0, ".")
from tree_search import Search
from tree_enum import run
for k in range(7, 15):
    t0 = time.time(); n2, l2, mr2, s2 = run(k, pmin=5, a=2, b=1, eps=-1)
    t1 = time.time(); S = Search(k, 2, 1, pmin=5, eps=-1); S.run()
    print(f"k={k:2d}  program 2: nodes={n2:6d} leaves={l2:6d} maxwidth={mr2:9d} solutions={s2} ({t1-t0:.1f}s)   "
          f"program 1: nodes={S.nodes:6d} solutions={S.sols} ({time.time()-t1:.1f}s)", flush=True)
    assert n2 == S.nodes and not s2 and not S.sols
print("No solution with omega(n) <= 14.  Hence omega(n) >= 15 for every composite n with phi(n) | n - 1.")
