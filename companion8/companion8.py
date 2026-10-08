#!/usr/bin/env python3
"""The companion equation with eight prime factors.

Every solution of phi(n) | n + 1 with omega(n) = 8 satisfies n + 1 = 2 phi(n) and 3 | n (Lemmas 2.2 and 2.3 and
Theorem 1.4), so n = p_1 ... p_8 with p_1 = 3.  This program runs the search of Section 3 with p_min = 3 down to
depth 5 (lastthree.frontier), keeps the prefixes that contain 3, and treats the last three primes s < p < q of each
prefix as follows.

  1. scan3 (mode 0) runs s over the admissible primes of the interval of the prefix and finds, for each s, every
     pair of integers p < q with  A s p q + 1 = 2 B (s-1)(p-1)(q-1)  whose entries satisfy the conditions that
     primes in this position satisfy (trial division for the small divisors of N, the sum of the two factors for
     the large ones).
  2. The values of s for which scan3 estimates more work than a complete factorisation are treated by
     factor_class.gp: N is factored completely by PARI/GP, every prime factor is proved prime, and all divisors of
     N in the class of Proposition 4.1 are listed.
  3. Every completion found is checked exactly, and p and q are tested for primality (a proof).

The intervals are cut into pieces, and a journal records each finished piece, so that an interrupted run resumes
where it stopped.

usage:  companion8.py [workers] [journal]
output: a report on stdout; the journal (one JSON line per piece) in data/companion8/journal.jsonl"""
import sys, os, json, time, math
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT); sys.path.insert(0, HERE)
import lastthree as L
from common import build, run_scan3, run_gp, line0, check_completion, sifted

KAPPA = 0.2          # ns: scan3 needs about KAPPA (N/c^3)^(1/2) ns for one s (measured on this prefix range)
FCOST = 4e6          # ns: about the time PARI/GP needs to factor N and prove its prime factors
SETUP = 1500.0       # ns per s
TARGET = 60e9        # ns of estimated work per piece


def cost_per_s(A, B, s):
    c = (2 * B - A) * s - 2 * B
    if c <= 0: return SETUP
    N = 2 * A * s * B * (s - 1) + c
    return SETUP + min(FCOST, KAPPA * math.sqrt(N / c ** 3))


def density(chosen, s):
    d = 1.0 / math.log(s)
    for q in chosen: d *= (q - 2) / (q - 1)
    return d


def piece_cost(chosen, A, B, a, b):
    """estimated work for s in [a, b]: sample at points spaced geometrically in c."""
    C = 2 * B - A
    ca, cb = max(C * a - 2 * B, 1), max(C * b - 2 * B, 1)
    pts = [a + (b - a) * i / 8 for i in range(9)] if C <= 0 else \
        [min(b, max(a, (math.exp(math.log(ca) + (math.log(cb) - math.log(ca)) * i / 8) + 2 * B) / C)) for i in range(9)]
    pts = sorted(set(int(p) for p in pts))
    tot = 0.0
    for u, v in zip(pts, pts[1:]):
        m = (u + v) // 2
        tot += (v - u) * density(chosen, m) * (cost_per_s(A, B, u) + cost_per_s(A, B, v) + 2 * cost_per_s(A, B, m)) / 4
    return max(tot, (b - a + 1) * density(chosen, a) * SETUP)


def split(chosen, A, B, lo, hi):
    out = []; stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        est = piece_cost(chosen, A, B, a, b)
        if est > TARGET and b - a > 20000:
            C = 2 * B - A
            ca, cb = max(C * a - 2 * B, 1), max(C * b - 2 * B, 1)
            m = (math.isqrt(ca * cb) + 2 * B) // C if C > 0 and cb > 4 * ca else (a + b) // 2
            m = min(max(m, a + 10000), b - 10000)
            stack += [(a, m), (m + 1, b)]
        else:
            out.append((a, b, est))
    return out


def pieces():
    fr = [x for x in L.frontier(8, 3, 2, 1, +1, 3) if 3 in x[0]]
    ps = []
    for chosen, A, B, lo, hi in fr:
        for a, b, est in split(chosen, A, B, lo, hi):
            ps.append((list(chosen), a, b, est))
    ps.sort(key=lambda x: -x[3])
    # batches of small pieces
    batches = []; cur = []; cur_est = 0.0
    for p in ps:
        if p[3] >= TARGET / 4:
            batches.append([p])
        else:
            cur.append(p); cur_est += p[3]
            if cur_est >= TARGET: batches.append(cur); cur = []; cur_est = 0.0
    if cur: batches.append(cur)
    return fr, batches


def key(p): return f"{','.join(map(str, p[0]))}:{p[1]}-{p[2]}"


def work(batch):
    t0 = time.time()
    lines = [line0(+1, chosen, a, b) for chosen, a, b, est in batch]
    tot, comps, defs = run_scan3(lines, (1.0, 0.11, FCOST))
    t1 = time.time()
    g, dmax, gsec = run_gp(defs, +1)
    allc = [list(c) for c in comps] + [list(c[:-2]) for c in g]
    for c in allc: assert check_completion(c, +1), c
    return dict(keys=[key(p) for p in batch], nx=int(tot["nx"]), nempty=int(tot["nempty"]), ntd=tot["ntd"],
                nsig=tot["nsig"], nsurv=int(tot["nsurv"]), ndef=len(defs), dmax=dmax, scan_sec=round(t1 - t0, 2),
                gp_sec=round(gsec, 2), completions=allc)


def main():
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    jpath = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "data", "companion8", "journal.jsonl")
    os.makedirs(os.path.dirname(jpath), exist_ok=True)
    build()
    t0 = time.time()
    fr, batches = pieces()
    width = sum(hi - lo + 1 for c, A, B, lo, hi in fr)
    npieces = sum(len(b) for b in batches)
    print(f"k = 8, n + 1 = 2 phi(n), 3 | n: {len(fr)} prefixes of five primes, total width of the intervals for p_6 "
          f"{width}, {npieces} pieces in {len(batches)} batches, estimated work "
          f"{sum(p[3] for b in batches for p in b) / 1e9 / 3600:.1f} processor hours", flush=True)
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
    # summary from the journal
    tot = dict(nx=0, nempty=0, ntd=0.0, nsig=0.0, nsurv=0, ndef=0, scan_sec=0.0, gp_sec=0.0); dmax = 0
    comps = []; seen = set()
    for l in open(jpath):
        if not l.strip(): continue
        r = json.loads(l)
        if any(k in seen for k in r["keys"]): continue
        seen.update(r["keys"])
        for k in tot: tot[k] += r[k]
        dmax = max(dmax, r["dmax"]); comps += [tuple(c) for c in r["completions"]]
    allkeys = {key(p) for b in batches for p in b}
    missing = allkeys - seen
    comps = sorted(set(comps))
    raw = len(comps)
    comps = [c for c in comps if sifted(c)]
    sols = [c for c in comps if all(L.proved_prime(x) for x in c)]
    print(f"pieces treated {len(seen & allkeys)} of {len(allkeys)}" + (f"; MISSING {len(missing)}" if missing else ""))
    print(f"admissible p_6 {tot['nx']}, with an empty range {tot['nempty']}; trial divisions {tot['ntd']:.4e}, values "
          f"of the sum {tot['nsig']:.4e}, candidates tested exactly {tot['nsurv']}; p_6 treated by factoring N "
          f"{tot['ndef']} (N up to {dmax} digits)")
    print(f"processor time: scan3 {tot['scan_sec'] / 3600:.2f} h, PARI/GP "
          f"{tot['gp_sec'] / 3600:.2f} h")
    print(f"completions s < p < q in integers: {raw} found, of which {len(comps)} with p and q free of prime factors "
          f"up to 61 (the others may be dropped by the filters of one route and reported by another)")
    for c in comps:
        print("   ", c[5:], "p prime" if L.proved_prime(c[6]) else "p composite",
              "q prime" if L.proved_prime(c[7]) else "q composite")
    print(f"solutions (all eight entries prime): {len(sols)} {sols}")
    print(f"wall {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
