"""Search of Proposition 2.5 of the paper: is there an independent set of at most K primes with prod p/(p-1) >= V ?

A set of primes is independent if no element divides another minus 1; the prime factors of a solution of
phi(n) | n -+ 1 form such a set (Lemma 2.1).  The allowed primes are those from 5 on, or with --mod3 those
congruent to 2 modulo 3 from 5 on.  Usage:
    python3 independent.py 2999999/1000000 16000            (Proposition 2.5(i))
    python3 independent.py 333333/125000 1000000 --mod3     (a part (ii) check at a small size)

The sets are built in increasing order.  A node S (product P, last prime p, m = K - |S| primes still free) has the
bound  P * prod p'/(p'-1)  over the m smallest allowed primes above p that are not = 1 modulo any prime of S; every
independent set of at most K primes whose smallest elements are S has product at most this bound, since p/(p-1)
decreases.  A node whose bound is below V is discarded.  A child S + {q} is created for each allowed q > p, not = 1
modulo a prime of S, whose bound computed without the condition imposed by q itself reaches V; this weaker bound
decreases with q, so the children are an initial run of the candidates.  Every node whose own product reaches V
is reported, so an independent set of at most K primes with product >= V is found if one exists.

Each node looks at a window of the prime table above its last prime, doubled until it holds the m primes of the
bound and the whole run of children.  Logarithms are summed in floating point; a bound within MARGIN of log V is
decided in exact rational arithmetic, and MARGIN exceeds the rounding error by many orders of magnitude.
"""
import sys, math, time, argparse
import numpy as np
from fractions import Fraction

MARGIN = 1e-7


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]


def exact_ge(primes, V):
    P = Fraction(1)
    for p in primes: P *= Fraction(int(p), int(p) - 1)
    return P >= V


class Short(Exception):
    pass


def expand(Q, LG, ch, pos, m, lp, logV, V, W):
    """(pruned, children, exact checks) for the node ch; raises Short if the window of W table entries is too small."""
    hi = min(len(Q), pos + 1 + W)
    tail = Q[pos + 1:hi]
    mask = np.ones(len(tail), dtype=bool)
    for p in ch: mask &= (tail % p) != 1
    adm = np.nonzero(mask)[0] + pos + 1               # table positions of the candidates above the last prime
    if len(adm) < m + 1:
        if hi == len(Q): raise RuntimeError("prime table too short")
        raise Short
    cum = np.concatenate(([0.0], np.cumsum(LG[adm])))
    ub = lp + cum[m]
    if ub < logV - MARGIN: return True, [], 0
    ex = 0
    if ub < logV + MARGIN:
        ex += 1
        if not exact_ge(list(ch) + [int(Q[t]) for t in adm[:m]], V): return True, [], ex
    nmax = len(adm) - m
    # bound of the child adm[s]: its own factor and the m - 1 candidates after it
    cb = lp + LG[adm[:nmax]] + (cum[m:m + nmax] - cum[1:1 + nmax])
    good = np.nonzero(cb >= logV - MARGIN)[0]
    if len(good) and good[-1] == nmax - 1:
        if hi == len(Q): raise RuntimeError("prime table too short for children")
        raise Short
    kids = []
    for s in good.tolist():
        if cb[s] < logV + MARGIN:
            ex += 1
            if not exact_ge(list(ch) + [int(Q[adm[s]])] + [int(Q[t]) for t in adm[s + 1:s + m]], V): continue
        kids.append(int(adm[s]))
    return False, kids, ex


def run(Q, LG, K, V, verbose=False):
    logV = math.log(V)
    nodes = 0; exact_checks = 0; bydepth = {}
    stack = [(-1, (), 4 * K + 1024)]
    t0 = time.time()
    while stack:
        pos, ch, W = stack.pop()
        nodes += 1; bydepth[len(ch)] = bydepth.get(len(ch), 0) + 1
        m = K - len(ch)
        lp = math.fsum(math.log(p / (p - 1)) for p in ch)
        if lp >= logV - MARGIN and exact_ge(ch, V):
            return list(ch), nodes, exact_checks, bydepth
        if m == 0: continue
        while True:
            try:
                pruned, kids, ex = expand(Q, LG, ch, pos, m, lp, logV, V, W); break
            except Short:
                W *= 2
        exact_checks += ex
        for t in reversed(kids):
            stack.append((t, ch + (int(Q[t]),), W))
        if verbose and nodes % 5000 == 0:
            print(f"   nodes {nodes}, depth {len(ch)}, stack {len(stack)}, {time.time() - t0:.0f} s", flush=True)
    return None, nodes, exact_checks, bydepth


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument('V'); ap.add_argument('K', type=int)
    ap.add_argument('--limit', type=int, default=30_000_000, help='primes up to this bound')
    ap.add_argument('--mod3', action='store_true', help='allowed primes: p = 2 mod 3, p >= 5')
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    V = Fraction(a.V)
    P = primes_upto(a.limit)
    Q = P[P >= 5]
    if a.mod3: Q = Q[Q % 3 == 2]
    LG = np.log(Q / (Q - 1.0))
    t0 = time.time()
    w, nodes, ex, bydepth = run(Q, LG, a.K, V, a.v)
    print(f"K = {a.K}, V = {V} ({float(V):.12f}), {'primes = 2 mod 3' if a.mod3 else 'primes >= 5'} up to {a.limit}")
    print(f"FOUND an independent set of {len(w)} primes: {w[:20]}" if w else "none")
    print(f"nodes {nodes}, max depth {max(bydepth)}, exact checks {ex}, {time.time() - t0:.1f} s")
    print("nodes by depth:", [bydepth.get(d, 0) for d in range(max(bydepth) + 1)])
