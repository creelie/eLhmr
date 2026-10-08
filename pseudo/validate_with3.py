#!/usr/bin/env python3
"""Validation of tail3 in integer mode with the entry 3 allowed (mode 2), for k = 3..7 and both signs.
Below the prime prefixes of the search with p_1 >= 3 (lastthree.frontier(k, 3, 2, 1, eps, 3)) its completions must be
exactly those solutions of  x_1 ... x_k + eps = 2 prod(x_i - 1)  in odd integers 3 <= x_1 < ... < x_k whose first k - 3
entries are prime.  The complete list of solutions is taken from pari_integer_tree.py --with3, which shares no code
with tail3; its output for k = 3..7 is recorded in logs/pari_integer_tree_with3.log.
usage: validate_with3.py [logs/pari_integer_tree_with3.log]"""
import sys, os, re, ast
from tail3lib import L, line_for, run
from sympy import isprime
here = os.path.dirname(os.path.abspath(__file__))
fn = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "logs", "pari_integer_tree_with3.log")
listed = {}; cur = None
for l in open(fn):
    m = re.match(r"k=(\d+) eps=([+-]1) with3=True", l)
    if m: cur = (int(m.group(1)), int(m.group(2))); listed[cur] = set(); continue
    if l.startswith("    (") and cur: listed[cur].add(tuple(ast.literal_eval(l.strip())))
allok = True
for eps in (-1, 1):
    for k in range(3, 8):
        lst = listed[(k, eps)]
        exp = {s for s in lst if all(isprime(x) for x in s[:k - 3])}
        fr = L.frontier(k, 3, 2, 1, eps, 3)
        lines = [line_for(c, lo, hi, eps, 2) for c, A, B, lo, hi in fr]
        tot, comps = run(lines, eps)
        got = {c for c, tag in comps}
        ok = got == exp
        allok &= ok
        print(f"eps={eps:+d} k={k}: {len(fr)} prime prefixes, t treated {tot['nt']}, deferred (factored) {tot['deferred']}, "
              f"completions {len(got)}, expected {len(exp)} of the {len(lst)} solutions, equal: {ok}", flush=True)
        for s in sorted(got): print("    ", s, "listed" if s in exp else "NOT LISTED")
        for s in sorted(exp - got): print("     MISSING", s)
print("VALIDATION", "PASSED" if allok else "FAILED")
