"""Search of Proposition 2.5(ii), (iii) of the paper, for very large sizes K: is there an independent set of at most K
primes q = 2 (mod 3), q >= 5, with prod q/(q-1) >= V ?  (Independent: no element divides another minus 1.)
Usage:
    python3 independent_stream.py 2e10 333333/125000 100000000      (part (ii): V = (8/3)(1 - 10^-6), K = 10^8)
    python3 independent_stream.py 2e10 333333/100000 100000000      (part (iii): V = (10/3)(1 - 10^-6))

The tree is that of independent.py: a node S has the bound  P(S) * prod q/(q-1)  over the m = K - |S| smallest primes
of the list above its last element that are not = 1 modulo any element of S, and its children are the first
candidates q whose bound, computed without the condition imposed by q itself, reaches V.  Here each node runs once
through a table of the primes = 2 (mod 3) up to X, stored as 16-bit gaps, and keeps only running counts and sums, so
memory stays small.  A node is discarded, or a child rejected, only if its bound is below log V - MARGIN, where
MARGIN = 10^-6 exceeds the worst-case rounding error of the double-precision sums (at most about 10^-8 here);
nothing is decided in the other direction, and a node whose own product comes within MARGIN of V is reported.
"""
import sys, math, time, argparse
import numpy as np

CH = 1 << 23            # chunk length (entries of the table)

def build(X, seg=1 << 27):
    """primes q = 2 mod 3 with 5 <= q <= X, as uint16 gaps plus checkpoints of absolute values every CH entries."""
    r = int(math.isqrt(X)) + 1
    s = np.ones(r + 1, dtype=bool); s[:2] = False
    for i in range(2, int(r ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    base = np.nonzero(s)[0]
    out = []; last = None; total = 0
    lo = 0
    t0 = time.time()
    while lo <= X:
        hi = min(X + 1, lo + seg)
        z = np.ones(hi - lo, dtype=bool)
        for p in base:
            p = int(p)
            if p * p >= hi: break
            st = max(p * p, ((lo + p - 1) // p) * p)
            z[st - lo::p] = False
        if lo == 0: z[:2] = False
        pr = np.nonzero(z)[0].astype(np.uint64) + np.uint64(lo)
        pr = pr[(pr % np.uint64(3) == 2) & (pr >= 5)]
        if len(pr):
            if last is None:
                g = np.diff(pr, prepend=np.uint64(0))        # first gap is the first prime itself (5)
            else:
                g = np.diff(pr, prepend=np.uint64(last))
            assert g.max() < 65536
            out.append(g.astype(np.uint16)); last = int(pr[-1]); total += len(pr)
        lo = hi
        print(f"   sieve {hi:.3e}  {total} primes = 2 mod 3  {time.time() - t0:.0f}s", flush=True, file=sys.stderr)
    gaps = np.concatenate(out)
    ck = [0]                                   # absolute value before chunk c
    for c in range(0, len(gaps), CH): ck.append(ck[-1] + int(gaps[c:c + CH].astype(np.uint64).sum()))
    return gaps, np.array(ck, dtype=np.uint64), last

class Table:
    def __init__(self, gaps, ck):
        self.gaps = gaps; self.ck = ck; self.n = len(gaps)
    def chunk(self, c):
        """(start index, primes) of chunk c."""
        a = c * CH; b = min(self.n, a + CH)
        return a, self.ck[c] + np.cumsum(self.gaps[a:b].astype(np.uint64))

MARGIN = 1e-6

def node(T, S, pos, m, lp, logV, rmax=1 << 20):
    """stream the candidates above table index pos.  Returns ('prune',) or ('kids', [(index, q)], info)."""
    first = []            # (index, q, lg) of the first candidates, as long as they may be children
    cnt = 0; acc = 0.0    # number and log-sum of the candidates seen
    Cm = None
    kids = []; t = 0      # next child candidate is first[t]; its bound needs the prefix sum up to candidate number t+m
    Cpref = []            # Cpref[i] = sum of lg over first[0..i-1]  (for i <= len(first))
    c = (pos + 1) // CH
    Sarr = [np.uint64(s) for s in S]
    while c * CH < T.n:
        a, pr = T.chunk(c)
        lo = max(0, pos + 1 - a)
        pr = pr[lo:]
        idx0 = a + lo
        mask = np.ones(len(pr), dtype=bool)
        for s in Sarr: mask &= (pr % s) != np.uint64(1)
        sel = np.nonzero(mask)[0]
        q = pr[sel]
        lg = np.log1p(1.0 / (q.astype(np.float64) - 1.0))
        cs = acc + np.cumsum(lg)                    # cs[i] = prefix sum through candidate number cnt + i + 1
        nq = len(q)
        # store the first few candidates (child candidates)
        if len(first) < rmax:
            take = min(nq, rmax - len(first))
            for i in range(take):
                first.append((int(idx0 + sel[i]), int(q[i]), float(lg[i])))
                Cpref.append(float(cs[i]))
        # node bound: prefix sum through candidate number m
        if Cm is None and cnt + nq >= m:
            Cm = float(cs[m - cnt - 1])
            if lp + Cm < logV - MARGIN: return ('prune',)
        # child bounds: candidate t (0-based) needs prefix sum through candidate number t + m  (its own lg plus m-1 next)
        while Cm is not None:
            need = t + m                              # candidate number whose prefix sum we need
            if need > cnt + nq: break
            if t >= len(first): raise RuntimeError("rmax too small")
            Ct_end = float(cs[need - cnt - 1])
            cb = lp + first[t][2] + (Ct_end - Cpref[t])  # lg(a_t) + sum over a_{t+1..t+m-1}
            if cb < logV - MARGIN:
                return ('kids', [(f[0], f[1]) for f in first[:t]], dict(R=t))
            t += 1
        cnt += nq; acc = float(cs[-1]) if nq else acc
        c += 1
    raise RuntimeError("table too short")

def search(T, K, V, verbose=True):
    logV = math.log(V)
    stack = [(-1, (), 0.0)]
    nodes = 0; depthcount = {}; t0 = time.time(); maxR = 0
    while stack:
        pos, S, lp = stack.pop()
        nodes += 1; depthcount[len(S)] = depthcount.get(len(S), 0) + 1
        if lp >= logV - MARGIN: return ('possible', S, nodes, depthcount)
        m = K - len(S)
        if m == 0: continue
        r = node(T, S, pos, m, lp, logV)
        if r[0] == 'prune': continue
        kids = r[1]; maxR = max(maxR, len(kids))
        for (i, q) in reversed(kids):
            stack.append((i, S + (q,), lp + math.log1p(1.0 / (q - 1))))
        if verbose:
            print(f"   node {nodes} S={S} children {len(kids)} {[q for i, q in kids[:12]]} stack {len(stack)} "
                  f"{time.time() - t0:.0f}s", flush=True, file=sys.stdout)
    return ('none', None, nodes, depthcount)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument('X', type=float); ap.add_argument('V'); ap.add_argument('K', type=float)
    ap.add_argument('--cache', help='file to keep the prime table in (.npz)')
    a = ap.parse_args()
    from fractions import Fraction
    import os
    V = Fraction(a.V); K = int(a.K)
    if a.cache and os.path.exists(a.cache):
        z = np.load(a.cache); gaps, ck, last = z['gaps'], z['ck'], int(z['last'])
    else:
        gaps, ck, last = build(int(a.X))
        if a.cache: np.savez(a.cache, gaps=gaps, ck=ck, last=np.array(last))
    T = Table(gaps, ck)
    print(f"table: {T.n} primes = 2 mod 3 from 5 to {last}", flush=True)
    t0 = time.time()
    res, S, nodes, dc = search(T, K, V)
    print(f"K = {K}, V = {V} ({float(V):.12f}): {res}{' ' + str(S) if S else ''}")
    print(f"nodes {nodes}, by depth {[dc.get(d, 0) for d in range(max(dc) + 1)]}, {time.time() - t0:.0f} s")
