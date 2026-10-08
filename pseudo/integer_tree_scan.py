#!/usr/bin/env python3
"""Theorem 9.3 (i) for k = 13: no odd integers 5 <= x_1 < ... < x_k, none divisible by 3, prime or not, satisfy
    x_1 ... x_k + eps = 2 (x_1 - 1) ... (x_k - 1).

The tree down to depth k - 3 is that of integer_tree.py (depth_k3_nodes).  At depth k - 3 the admissible values of
x_{k-2} in the interval of each node are passed to the program scan3 of ../companion8 in mode 1 (odd integers prime
to 3, with x != 0 mod the odd primes of the earlier x_i - 1 and x != 1 mod the primes of the earlier x_i), which finds
every completion (x, p, q) in integers prime to 3 by trial division and by the sum of the two factors, and passes the
values of x for which this would be slow to PARI/GP, which factors N completely, proves every prime factor prime and
lists the divisors of N in the class (factor_class.gp).  The intervals are cut into pieces of about equal estimated
work, and a journal records each finished batch of pieces, so that an interrupted run resumes where it stopped.

usage:  integer_tree_scan.py k eps [workers] [journal]
output: a report on stdout; the journal in data/pseudo/integer_tree_k{k}_{m1|p1}.jsonl"""
import sys, os, json, time, math
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, "companion8"))
import integer_tree as IT
from tail3lib import odd_primes_of
from common import build, run_scan3, run_gp, check_completion

WIDTH = 2 * 10 ** 8          # largest number of integers x in a piece
WORK = 60.0                  # estimated seconds per piece and per batch
PARAMS = (1.0, 0.11, 8e7)    # scan3: cost weights, and the estimate (ns) above which N is factored instead
FACTOR_SEC = 0.17            # PARI/GP, complete factorisation of N (about 54 digits) with proofs
EPS = None


def line1(eps, xs, lo, hi):
    R0 = odd_primes_of([x - 1 for x in xs]); R1 = odd_primes_of(list(xs))
    return (f"{eps} 1 {len(xs)} {' '.join(map(str, xs))} {lo} {hi} {len(R0)} {' '.join(map(str, R0))} "
            f"{len(R1)} {' '.join(map(str, R1))}")


def key(p): return f"{','.join(map(str, p[0]))}:{p[1]}-{p[2]}"


def seconds_per_x(A, B, x):
    """estimated time for one admissible x: the estimate of scan3 (same formula, PARAMS), or the factoring of N."""
    a1, a2, fcost = PARAMS
    Ap = A * x; Bp = B * (x - 1); c = 2 * Bp - Ap
    if c <= 0: return 1e-6
    N = 2.0 * Ap * Bp; sN = math.sqrt(N); tm = max(c * (x + 2.0) - 2.0 * Bp, 1.0)
    if tm > sN: return 1e-6
    ts = min(max(math.sqrt(N / (1 + a1 * c * 2 / a2)), tm), sN + 1)
    nsig = ((ts + N / ts - 2 * sN) / c) / (c * 2)                  # values of the sum
    est = a1 * (ts - tm) / c + a2 * nsig
    return FACTOR_SEC if est > fcost else 1.4e-9 * est + 1e-6 + (4e-6 if nsig > 100 else 0)


def cut(xs, lo, hi):
    """cut [lo, hi] into pieces of estimated work about WORK seconds; returns [(a, b, seconds)]."""
    A = math.prod(xs); B = math.prod(x - 1 for x in xs); C = 2 * B - A
    dens = 1 / 3                                                  # odd and prime to 3
    for r in set(odd_primes_of([x - 1 for x in xs]) + odd_primes_of(list(xs))):
        if r > 3: dens *= 1 - 1 / r
    # sample points spaced geometrically in c = C x - 2B, on which the cost depends
    c0 = max(C * lo - 2 * B, 1); c1 = max(C * hi - 2 * B, 2); M = 200
    pts = sorted({lo, hi + 1} | {int((c0 * (c1 / c0) ** (i / M) + 2 * B) / C) for i in range(M + 1)})
    pts = [x for x in pts if lo <= x <= hi + 1]
    out = []; a = lo; w = 0.0
    for u, v in zip(pts, pts[1:]):
        rate = dens * seconds_per_x(A, B, (u + v) // 2)       # seconds per integer in [u, v)
        while u < v:
            room = min((WORK - w) / rate, a + WIDTH - u)          # integers that still fit into the current piece
            if v - u < room:
                w += (v - u) * rate; u = v
            else:
                b = u + max(1, int(room)); w += (b - u) * rate
                out.append((a, b - 1, w)); a = b; u = b; w = 0.0
    if a <= hi: out.append((a, hi, w))
    return out


def pieces(k, eps):
    nodes, visited = IT.depth_k3_nodes(k, eps)
    ps = [(list(xs), a, b, w) for xs, lo, hi in nodes for a, b, w in cut(xs, lo, hi)]
    batches = []; cur = []; w = 0.0
    for p in sorted(ps, key=lambda p: -p[3]):
        cur.append(p); w += p[3]
        if w >= WORK: batches.append(cur); cur = []; w = 0.0
    if cur: batches.append(cur)
    return nodes, visited, batches


def work(batch):
    t0 = time.time()
    tot, comps, defs = run_scan3([line1(EPS, *p[:3]) for p in batch], PARAMS)
    t1 = time.time()
    g, dmax, gsec = run_gp(defs, EPS)
    # the routes may also report completions with p or q divisible by 3; only those prime to 3 are sought
    allc = sorted(c for c in {tuple(c) for c in comps} | {tuple(c[:-2]) for c in g} if c[-1] % 3 and c[-2] % 3)
    for c in allc: assert check_completion(c, EPS), c
    return dict(keys=[key(p) for p in batch], nx=int(tot["nx"]), nempty=int(tot["nempty"]), ntd=tot["ntd"],
                nsig=tot["nsig"], nsurv=int(tot["nsurv"]), ndef=len(defs), dmax=dmax, scan_sec=round(t1 - t0, 2),
                gp_sec=round(gsec, 2), completions=[list(c) for c in allc])


def main():
    global EPS
    k = int(sys.argv[1]); EPS = int(sys.argv[2])
    W = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    jpath = sys.argv[4] if len(sys.argv) > 4 else os.path.join(
        ROOT, "data", "pseudo", f"integer_tree_k{k}_{'m1' if EPS < 0 else 'p1'}.jsonl")
    os.makedirs(os.path.dirname(jpath), exist_ok=True)
    build(); t0 = time.time()
    nodes, visited, batches = pieces(k, EPS)
    width = sum(hi - lo + 1 for xs, lo, hi in nodes)
    npieces = sum(len(b) for b in batches); hours = sum(p[3] for b in batches for p in b) / 3600
    print(f"k = {k}, eps = {EPS:+d}: {visited} nodes visited, {len(nodes)} nodes at depth {k - 3}, total width of "
          f"the intervals for x_{k - 2} {width}, {npieces} pieces in {len(batches)} batches, estimated work "
          f"{hours:.1f} processor hours", flush=True)
    done = set()
    if os.path.exists(jpath):
        for l in open(jpath):
            if l.strip(): done.update(json.loads(l)["keys"])
    todo = [b for b in batches if not all(key(p) in done for p in b)]
    print(f"{len(batches) - len(todo)} batches already in the journal, {len(todo)} to do", flush=True)
    with Pool(W) as P, open(jpath, "a") as J:
        for i, r in enumerate(P.imap_unordered(work, todo)):
            J.write(json.dumps(r) + "\n"); J.flush()
            if i % 50 == 0 or i == len(todo) - 1:
                print(f"  {i + 1}/{len(todo)} batches, {time.time() - t0:.0f}s", flush=True)
    tot = dict(nx=0, nempty=0, ntd=0.0, nsig=0.0, nsurv=0, ndef=0, scan_sec=0.0, gp_sec=0.0); dmax = 0
    comps = set(); seen = set()
    for l in open(jpath):
        if not l.strip(): continue
        r = json.loads(l)
        if any(x in seen for x in r["keys"]): continue
        seen.update(r["keys"])
        for x in tot: tot[x] += r[x]
        dmax = max(dmax, r["dmax"]); comps |= {tuple(c) for c in r["completions"]}
    allkeys = {key(p) for b in batches for p in b}
    missing = allkeys - seen
    print(f"pieces treated {len(seen & allkeys)} of {len(allkeys)}" + (f"; MISSING {len(missing)}" if missing else ""))
    print(f"admissible x_{k - 2} {tot['nx']}; trial divisions {tot['ntd']:.4e}, values of the sum {tot['nsig']:.4e}, "
          f"candidates tested exactly {tot['nsurv']}; x treated by factoring N {tot['ndef']} (N up to {dmax} digits)")
    print(f"processor time: scan3 {tot['scan_sec'] / 3600:.2f} h, PARI/GP {tot['gp_sec'] / 3600:.2f} h")
    print(f"completions in odd integers prime to 3: {len(comps)}")
    for c in sorted(comps): print("   COMPLETION", c)
    print(f"wall {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
