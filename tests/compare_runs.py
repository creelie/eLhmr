#!/usr/bin/env python3
"""Task-by-task comparison of the k = 15 runs of the three implementations (data/k15/run_*.jsonl).

For each sign of epsilon, every one of the 55,443 tasks must appear in the runs of all three programs, with the
same number of admissible primes p_13 and with no candidate completion and no solution in any of them."""
import json, sys, os, gzip, collections

def load(path):
    rows = collections.defaultdict(list)
    f = open(path) if os.path.exists(path) else gzip.open(path + ".gz", "rt")    # archived runs are gzipped
    for line in f:
        r = json.loads(line); rows[tuple(r["task"])].append(r)
    return rows

ok = True
for names in (("run_A", "run_B", "run_C"), ("run_A_plus", "run_B_plus", "run_C_plus")):
    R = [load(f"data/k15/{n}.jsonl") for n in names]
    dup = [sum(len(v) > 1 for v in X.values()) for X in R]
    same_tasks = all(set(X) == set(R[0]) for X in R)
    diff_ns = [t for t in R[0] if len({r["n_s"] for X in R for r in X.get(t, [])}) != 1]
    found = [(t, r) for X in R for t in X for r in X[t] if r["sols"] or r["cands"]]
    n_s = sum(R[0][t][0]["n_s"] for t in R[0])
    good = same_tasks and not diff_ns and not found and len(R[0]) == 55443
    ok &= good
    print(f"{' vs '.join(names)}: tasks {' / '.join(str(len(X)) for X in R)}, same task set {same_tasks}, "
          f"repeated tasks {dup}, tasks with different counts of p_13: {len(diff_ns)}, total p_13 {n_s}, "
          f"tasks with candidates or solutions: {len(found)} -> {'agree' if good else 'DISAGREE'}")
print("all runs agree" if ok else "RUNS DISAGREE")
sys.exit(0 if ok else 1)
