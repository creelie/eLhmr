#!/usr/bin/env python3
"""Repetition of part of the eight-prime search with other parameters.

A random sample of the pieces of companion8.py (seeded, so that the sample is reproducible) is run again with the
cost weights and the factoring threshold changed: a1 = 1.0, a2 = 0.35 (the sums are taken to cost more than three
times as much as in the run, so that the split point t_d moves) and a threshold of 1.5 ms (so that a different set of
integers N is factored).  For every piece, the number of admissible values of p_6 and the set of completions with
p and q free of prime factors up to 61 (common.sifted; every route finds all of these) must equal those recorded in
the journal of the run.  Every piece containing the sixth entry of a recorded completion is repeated as well; when
it was run in a batch with other pieces, only its completions are compared.

usage:  recheck.py [fraction] [workers] [journal]      (defaults 0.03, 4, data/companion8/journal.jsonl)"""
import sys, os, json, random, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT); sys.path.insert(0, HERE)
from common import build, run_scan3, run_gp, line0, check_completion, sifted
from companion8 import pieces, key

PARAMS = (1.0, 0.35, 1.5e6)


def one(p):
    chosen, a, b, est = p
    tot, comps, defs = run_scan3([line0(+1, chosen, a, b)], PARAMS)
    g, dmax, gsec = run_gp(defs, +1)
    allc = sorted({tuple(c) for c in comps} | {tuple(c[:-2]) for c in g})
    for c in allc: assert check_completion(c, +1), c
    return key(p), int(tot["nx"]), len(defs), [c for c in allc if sifted(c)]


def main():
    frac = float(sys.argv[1]) if len(sys.argv) > 1 else 0.03
    W = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    jpath = sys.argv[3] if len(sys.argv) > 3 else os.path.join(ROOT, "data", "companion8", "journal.jsonl")
    build(); t0 = time.time()
    fr, batches = pieces()
    # the journal records totals per batch; single-piece batches give the count per piece
    single = {}; recorded = set()
    for l in open(jpath):
        if not l.strip(): continue
        r = json.loads(l)
        recorded |= {tuple(c) for c in r["completions"] if sifted(c)}
        if len(r["keys"]) == 1:
            single[r["keys"][0]] = r["nx"]
    def expected(p):
        return sorted(c for c in recorded if list(c[:5]) == p[0] and p[1] <= c[5] <= p[2])
    allp = [p for b in batches for p in b if len(b) == 1 and key(p) in single]
    random.seed(20261002)
    sample = random.sample(allp, max(1, int(frac * len(allp))))
    # also every piece that contains a recorded completion
    withc = [p for b in batches for p in b if expected(p)]
    sample += [p for p in withc if p not in sample]
    bad = 0; nx = 0; ndef = 0; ncomp = 0
    with Pool(W) as P:
        for k, n, nd, comps in P.imap_unordered(one, sample):
            p = next(p for p in sample if key(p) == k)
            nx += n; ndef += nd; ncomp += len(comps)
            if comps != expected(p) or (k in single and n != single[k]):
                bad += 1; print("MISMATCH", k, n, comps, single.get(k), expected(p), flush=True)
    print(f"{len(sample) - len(withc)} of {len(allp)} single-piece batches and the {len(withc)} pieces with a completion "
          f"repeated with parameters {PARAMS}: admissible p_6 {nx}, factored {ndef}, completions {ncomp}; "
          f"mismatches {bad}  ({time.time() - t0:.0f}s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
