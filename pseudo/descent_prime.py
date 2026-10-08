#!/usr/bin/env python3
"""The defect descent of pseudo/descent.py with every entry required to be prime.

A node is an increasing tuple of primes x >= 5 with A = prod x, B = prod (x - 1), defect c = 2B - A > 0.
Its children are the primes x = x0 + i (i >= i_lo) with x - 1 prime to A, of defect c' = r0 + i c, where
r0 = (-2B) mod c and x0 = (2B + r0)/c (exactly as in descent.py).  Generation g+1 keeps the N prime children of
generation g with the smallest defect (exact top N: candidates are tested in increasing order of c').
Every node is tested for a last entry X = (2B - 1)/c, which would give a solution of x_1 ... x_k X - 1 = 2 prod(x - 1);
if X is a probable prime that is a Lehmer number and is reported.
Reported per generation: nodes, sum 1/c (expected integer closures) and sum 2/(c log X) (expected prime closures)."""
import sys, math, time, pickle, argparse
import numpy as np
import multiprocessing as mp
from gmpy2 import mpz, gcd as mgcd, is_bpsw_prp

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
SMALL = primes_upto(3000)
PRIM = mpz(1)
for p in SMALL: PRIM *= p
VEC = [p for p in SMALL if p <= 400]
SMALLSET = set(SMALL)

def node(xs):
    A = mpz(1); B = mpz(1)
    for x in xs: A *= x; B *= x - 1
    return dict(xs=tuple(mpz(x) for x in xs), A=A, B=B, c=int(2 * B - A))

def prep(s):
    c = s['c']
    r0 = int((-2 * s['B']) % c)
    x0 = (2 * s['B'] + r0) // c
    xl = s['xs'][-1]
    i_lo = 0 if x0 > xl else int(xl - x0) + 1
    s['r0'] = r0; s['x0'] = x0; s['i_lo'] = i_lo
    s['x0p'] = int(x0 % PRIM)
    s['big'] = [int(x) for x in s['xs'] if x > 3000]          # prefix primes not covered by the sieve
    s['smallA'] = [int(x) for x in s['xs'] if x <= 3000]

def cands(s, Tlo, Thi):
    """sieved candidate indices i with Tlo < c' <= Thi; returns list of (c', i)."""
    c = s['c']; r0 = s['r0']
    lo = max(s['i_lo'], (Tlo - r0) // c + 1 if Tlo >= r0 else 0)
    hi = (Thi - r0) // c
    if hi < lo: return []
    x0p = s['x0p']
    out = []
    while lo <= hi and s['x0'] + lo <= 3000:                  # small x: decided directly
        x = int(s['x0'] + lo)
        if x in SMALLSET and all((x - 1) % q for q in s['smallA']): out.append((r0 + lo * c, lo))
        lo += 1
    if hi < lo: return out
    if hi - lo > 200:
        ii = np.arange(lo, hi + 1, dtype=np.int64)
        for p in VEC:
            rp = x0p % p
            ii = ii[(rp + ii) % p != 0]                       # x has no factor p <= 400
            if p in s['smallA']: ii = ii[(rp + ii) % p != 1]  # p does not divide x - 1
        ii = ii.tolist()
    else:
        ii = [i for i in range(lo, hi + 1)
              if all((x0p + i) % p for p in VEC) and all((x0p + i) % p != 1 for p in s['smallA'] if p <= 400)]
    for i in ii:
        xr = x0p + i
        if mgcd(xr, PRIM) != 1: continue
        if any((xr - 1) % p == 0 for p in s['smallA']): continue
        out.append((r0 + i * c, i))
    return out

def test(args):
    """primality of x0 + i for the given (node, i); also x - 1 prime to the large prefix primes."""
    j, i = args
    s = G['nodes'][j]
    x = s['x0'] + i
    for q in s['big']:
        if (x - 1) % q == 0: return False
    return bool(is_bpsw_prp(x))

G = {}

def closure(s):
    c = s['c']
    r = []
    for eps in (-1, 1):
        if (2 * s['B'] + eps) % c == 0:
            X = (2 * s['B'] + eps) // c
            if X > s['xs'][-1]:
                ok = X % 3 != 0 and mgcd(X - 1, s['A']) == 1 and mgcd(X, s['B']) == 1
                pr = bool(is_bpsw_prp(X)) if ok else False
                r.append((eps, int(c), ok, pr, len(s['xs']) + 1, X.bit_length()))
    return r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seeds', required=True)
    ap.add_argument('--N', type=int, default=2000)
    ap.add_argument('--gens', type=int, default=8)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--maxdigits', type=int, default=3000)
    a = ap.parse_args()
    pre = pickle.load(open(a.seeds, 'rb'))
    nodes = []
    for p, c in sorted(pre.items()):
        if len(p) < 8 or c <= 0: continue
        B = 1
        for x in p: B *= x - 1
        if 2 * B <= c * p[-1]: continue
        nodes.append(node(p))
    print(f"seeds {len(nodes)} N={a.N}", flush=True)
    tot_int = 0.0; tot_pr = 0.0; t00 = time.time()
    for g in range(a.gens + 1):
        t0 = time.time()
        mass = 0.0; pmass = 0.0; hits = []
        for s in nodes:
            prep(s)
            mass += 1.0 / s['c']
            X = 2 * s['B'] // s['c']
            pmass += 2.0 / (s['c'] * (X.bit_length() * math.log(2)))
            hits += closure(s)
        tot_int += mass; tot_pr += pmass
        cs = [s['c'] for s in nodes]
        digits = max(len(str(s['xs'][-1])) for s in nodes)
        print(f"gen {g}: nodes {len(nodes)} c min {min(cs)} max {max(cs):.3e} last-entry digits <= {digits} "
              f"sum 1/c {mass:.3e} (total {tot_int:.3e})  sum 2/(c log X) {pmass:.3e} (total {tot_pr:.3e})", flush=True)
        for h in hits:
            print(f"   closure eps={h[0]:+d} c={h[1]} k={h[4]} X bits {h[5]} conditions {h[2]} probable prime {h[3]}", flush=True)
            if h[3] and h[0] == -1: print("   *** LEHMER CANDIDATE ***", flush=True)
        if g == a.gens or digits > a.maxdigits: break
        # next generation: exact top N prime children by defect
        G['nodes'] = nodes
        T = max(cs) * 4
        Tlo = -1; found = []; tested = 0
        pool = mp.get_context('fork').Pool(a.workers)
        while len(found) < a.N:
            cl = []
            for j, s in enumerate(nodes):
                for cp, i in cands(s, Tlo, T): cl.append((cp, j, i))
            cl.sort()
            B_ = 64 * a.workers
            for k0 in range(0, len(cl), B_):
                chunk = cl[k0:k0 + B_]
                res = pool.map(test, [(j, i) for cp, j, i in chunk], chunksize=8)
                tested += len(chunk)
                for (cp, j, i), ok in zip(chunk, res):
                    if ok: found.append((cp, j, i))
                if len(found) >= a.N: break
            if len(found) >= a.N: break
            Tlo = T; T *= 4
        pool.close()
        found.sort(); found = found[:a.N]
        new = []
        for cp, j, i in found:
            s = nodes[j]
            x = s['x0'] + i
            t = dict(xs=s['xs'] + (x,), A=s['A'] * x, B=s['B'] * (x - 1), c=int(cp))
            assert t['c'] == 2 * t['B'] - t['A']
            new.append(t)
        print(f"   tested {tested} candidates for {len(found)} prime children, threshold {T:.3e}, "
              f"{time.time() - t0:.0f}s [{time.time() - t00:.0f}s]", flush=True)
        nodes = new

main()
