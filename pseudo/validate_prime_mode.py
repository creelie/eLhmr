#!/usr/bin/env python3
"""Validation of tail3 against the recorded case k = 15 of Theorems 1.1 and 1.4: in prime mode (mode 0) on the 54,985
prefixes of data/k15/frontier.json it must treat the same 33,865,004 values of p_13 as the three programs of the
repository (logs/k15_run_*.log) and find no completion.
usage: validate_prime_mode.py eps"""
import sys, os, json
from tail3lib import line_for, run
eps = int(sys.argv[1])
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fr = json.load(open(os.path.join(root, "data", "k15", "frontier.json")))
lines = [line_for(c, lo, hi, eps, 0) for c, lo, hi in fr]
tot, comps = run(lines, eps)
print(f"prime mode k=15 eps={eps:+d}: prefixes {tot['tasks']}, p13 treated {tot['nt']}, single {tot['single']}, "
      f"multi {tot['multi']}, deferred (factored) {tot['deferred']}, completions {len(comps)}, cpu {tot['cpu']:.1f}s")
ok = tot['nt'] == 33865004 and len(comps) == 0
print("VALIDATION", "PASSED" if ok else "FAILED")
