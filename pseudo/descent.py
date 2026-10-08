#!/usr/bin/env python3
"""Defect descent with selection, memory-light, parallel.

A node is an increasing tuple of odd integers x >= 5 prime to 3 with gcd(x_i, x_j - 1) = 1, A = prod x, B = prod (x - 1),
defect c = 2B - A > 0.  Its children are x = x0 + i (i >= i_lo), with defect c' = r0 + i c, r0 = (-2B) mod c,
x0 = (2B + r0)/c.  Generation g+1 consists of the N admissible children of generation g with the smallest defect.
Only (parent index, i, c) is stored per node; A and B are recomputed along the paths in each pass.
Every node is tested for one-entry closure:
    c | 2B - 1 :  X = (2B - 1)/c  gives  x_1 ... x_k X - 1 = 2 prod (x - 1)     (Lehmer sign)
    c | 2B + 1 :  X = (2B + 1)/c  gives  x_1 ... x_k X + 1 = 2 prod (x - 1)     (companion sign)
Any hit is verified with exact integers (equation, order, oddness, 3 does not divide, all gcd(x_i, x_j - 1) = 1)."""
import sys, os, math, time, pickle, argparse
import numpy as np
import multiprocessing as mp
from gmpy2 import mpz, gcd as mgcd

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
SP = [p for p in primes_upto(3000) if p > 3]
PSP = 1
for p in SP: PSP *= p
PSP_I = PSP
PSP = mpz(PSP)

def verify(xs, eps):
    X = mpz(1); Phi = mpz(1)
    for i, x in enumerate(xs):
        if x < 5 or x % 2 == 0 or x % 3 == 0: return False, 'entry'
        if i and x <= xs[i-1]: return False, 'order'
        X *= x; Phi *= (x - 1)
    if X + eps != 2 * Phi: return False, 'equation'
    # gcd(x_i, x_j - 1) = 1 for all i, j  <=>  gcd(x_i, Phi) = 1 for all i
    for x in xs:
        if mgcd(mpz(x), Phi) != 1: return False, 'gcd'
    return True, 'ok'

G = {}   # globals inherited by forked workers: seeds, gens

def child_state(st, i, cp):
    """state of child i of st, whose defect cp = r0 + i c is known; A is not needed (A = 2B - c)."""
    x = st['x0'] + i
    B = st['B'] * (x - 1)
    xr = (st['x0r'] + i) % PSP
    gx = mgcd(xr, PSP); gx1 = mgcd(xr - 1, PSP)
    PA = st['PA'] * gx // mgcd(st['PA'], gx)
    PB = st['PB'] * gx1 // mgcd(st['PB'], gx1)
    s = dict(B=B, c=cp, xl=x, PA=PA, PB=PB, xs=st['xs'] + (x,))
    prep(s)
    return s

def prep(s):
    c = s['c']
    b = int(s['B'] % c); s['b'] = b
    r0 = (-2 * b) % c
    x0 = (2 * s['B'] + r0) // c
    s['r0'] = r0; s['x0'] = x0; s['x0r'] = x0 % PSP; s['x06'] = int(x0 % 6)

def seed_state(xs):
    A = mpz(1); B = mpz(1)
    for x in xs: A *= x; B *= x - 1
    PA = mpz(1); PB = mpz(1)
    for p in SP:
        if A % p == 0: PA *= p
        if B % p == 0: PB *= p
    s = dict(B=B, c=int(2 * B - A), xl=xs[-1], PA=PA, PB=PB, xs=tuple(mpz(x) for x in xs))
    prep(s)
    return s

def candidates(s, T):
    """admissible children with c' <= T: arrays (cprime, i)."""
    c = s['c']; r0 = s['r0']; x0 = s['x0']
    i_lo = 0 if x0 > s['xl'] else int(s['xl'] - x0) + 1
    if r0 + i_lo * c > T: return None
    i_hi = (T - r0) // c
    n = i_hi - i_lo + 1
    PA = s['PA']; PB = s['PB']
    if n > 64:
        ii = np.arange(i_lo, i_hi + 1, dtype=np.int64)
        x06 = s['x06']
        m = ((x06 + ii) % 2) == 1
        m &= ((x06 + ii) % 3) != 0
        ii = ii[m]
        # small primes, vectorised for the primes up to 200, then exact gcd for the survivors
        rb = s['x0r'] % PB; ra = (s['x0r'] - 1) % PA
        for p in SP:
            if p > 200: break
            if PB % p == 0: ii = ii[((rb % p + ii) % p) != 0]
            elif PA % p == 0: ii = ii[((ra % p + ii) % p) != 0]
        keep = [i for i in ii.tolist() if mgcd(rb + i, PB) == 1 and mgcd(ra + i, PA) == 1]
        if not keep: return None
        ii = np.array(keep, dtype=np.int64)
    else:
        x0m6 = s['x06']
        rb = s['x0r'] % PB; ra = (s['x0r'] - 1) % PA
        keep = []
        for i in range(i_lo, i_hi + 1):
            if (x0m6 + i) % 6 not in (1, 5): continue
            if mgcd(rb + i, PB) != 1 or mgcd(ra + i, PA) != 1: continue
            keep.append(i)
        if not keep: return None
        ii = np.array(keep, dtype=np.int64)
    return r0 + ii * c, ii

def closure(s, hits, g):
    c = s['c']; b = s['b']
    for eps in (-1, 1):
        if (2 * b + eps) % c == 0:
            X = (2 * s['B'] + eps) // c
            if X <= s['xl']: continue
            t = s['xs'] + (X,)
            ok, why = verify(t, eps)
            hits.append((eps, g, len(t), c, ok, why, [int(v) for v in t] if ok else None))
            print(f"*** HIT eps={eps:+d} gen {g} k={len(t)} c={c} verify={ok} ({why})", flush=True)

def work(args):
    """process generation g nodes lo..hi-1: closure tests and candidate children with c' <= T."""
    g, lo, hi, T, outpath = args
    seeds = G['seeds']; gens = G['gens']
    # path of node j at gen g: indices at each gen
    def path(j):
        p = [j]
        for h in range(g, 0, -1):
            p.append(int(gens[h]['par'][p[-1]]))
        return p[::-1]           # [seed index, idx at gen1, ..., idx at gen g]
    stack = []                   # stack[h] = (index at gen h, state)
    cs_out = []; par_out = []; i_out = []; hits = []; mass = 0.0; nodes = 0; bits = 0
    for j in range(lo, hi):
        p = path(j)
        h0 = 0
        while h0 < len(stack) and stack[h0][0] == p[h0]: h0 += 1
        del stack[h0:]
        for h in range(h0, g + 1):
            if h == 0:
                st = seeds[p[0]]
            else:
                i = int(gens[h]['i'][p[h]])
                cp = int(gens[h]['c'][p[h]])
                par = stack[-1][1]
                assert cp == par['r0'] + i * par['c']
                st = child_state(par, i, cp)
            stack.append((p[h], st))
        s = stack[-1][1]
        nodes += 1; mass += 1.0 / s['c']; bits = max(bits, int(s['B'].bit_length()))
        closure(s, hits, g)
        r = candidates(s, T)
        if r is not None:
            cs_out.append(r[0]); i_out.append(r[1]); par_out.append(np.full(len(r[0]), j, dtype=np.int64))
    if cs_out:
        cs = np.concatenate(cs_out); ii = np.concatenate(i_out); pp = np.concatenate(par_out)
    else:
        cs = np.zeros(0, np.int64); ii = cs.copy(); pp = cs.copy()
    np.savez(outpath, c=cs, i=ii, par=pp)
    return dict(hits=hits, mass=mass, nodes=nodes, bits=bits)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--N', type=int, default=20000)
    ap.add_argument('--gens', type=int, default=10)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--q', type=float, default=1.6, help='candidate threshold = max c of generation / q')
    ap.add_argument('--rho', type=float, default=0.15)
    ap.add_argument('--tmp', default='tmp')
    ap.add_argument('--out', default='descent_out.pkl')
    ap.add_argument('--seeds', default='prefixes_k13.pkl')
    a = ap.parse_args()
    os.makedirs(a.tmp, exist_ok=True)
    pre = pickle.load(open(a.seeds, 'rb'))
    seeds = []
    for p, c in sorted(pre.items()):
        if len(p) < 8 or c <= 0: continue
        A = 1; B = 1
        for x in p: A *= x; B *= x - 1
        if 2 * B <= c * p[-1]: continue          # not closable yet
        seeds.append(seed_state(p))
    G['seeds'] = seeds; G['gens'] = [None]
    M0 = sum(1.0 / s['c'] for s in seeds)
    print(f"seeds {len(seeds)} mass {M0:.3e} N={a.N} workers={a.workers}", flush=True)
    allhits = []; tot = 0.0
    T = int(1.3 * a.N / (a.rho * M0))
    t00 = time.time()
    for g in range(0, a.gens + 1):
        t0 = time.time()
        n = len(seeds) if g == 0 else len(G['gens'][g]['c'])
        W = a.workers
        bounds = [n * w // W for w in range(W + 1)]
        jobs = [(g, bounds[w], bounds[w + 1], T, f"{a.tmp}/cand_{w}.npz") for w in range(W) if bounds[w + 1] > bounds[w]]
        if W > 1:
            with mp.get_context('fork').Pool(len(jobs)) as pool: res = pool.map(work, jobs)
        else:
            res = [work(j) for j in jobs]
        mass = sum(r['mass'] for r in res); tot += mass
        for r in res: allhits += r['hits']
        bits = max(r['bits'] for r in res)
        cs = []; ii = []; pp = []
        for jb in jobs:
            d = np.load(jb[4]); cs.append(d['c']); ii.append(d['i']); pp.append(d['par'])
        cs = np.concatenate(cs); ii = np.concatenate(ii); pp = np.concatenate(pp)
        ncand = len(cs)
        print(f"gen {g}: nodes {n} mass {mass:.3e} total {tot:.3e} maxbits {bits} hits {len(allhits)}; "
              f"candidates {ncand} (T {T:.3e}) {time.time()-t0:.0f}s  [{time.time()-t00:.0f}s]", flush=True)
        if g == a.gens or ncand == 0: break
        if ncand > a.N:
            sel = np.argpartition(cs, a.N - 1)[:a.N]
        else:
            sel = np.arange(ncand)
        order = sel[np.lexsort((ii[sel], pp[sel]))]
        G['gens'].append(dict(c=cs[order].copy(), i=ii[order].copy(), par=pp[order].copy()))
        cmax = int(G['gens'][-1]['c'].max()); cmin = int(G['gens'][-1]['c'].min())
        print(f"   gen {g+1} selected {len(order)}: c min {cmin} max {cmax:.3e}", flush=True)
        T = int(cmax / a.q)
        del cs, ii, pp
        pickle.dump(dict(hits=allhits, args=vars(a)), open(a.out, 'wb'))
    pickle.dump(dict(hits=allhits, args=vars(a)), open(a.out, 'wb'))
    print("HITS", allhits, flush=True)

if __name__ == "__main__":
    main()
