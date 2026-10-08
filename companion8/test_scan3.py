#!/usr/bin/env python3
"""Tests of scan3 against known answers and against complete factorisation.

1. Prime entries (mode 0), n + 1 = 2 phi(n), p_1 >= 3, k = 3..7: the prime completions must be exactly the known
   solutions 255, 65535, 83623935, 4294967295, 6992962672132095.  The three routes below must agree on the
   completions whose last two entries satisfy the conditions that scan3 imposes on prime entries (they may differ
   on completions by composite p or q that violate these conditions, which the filters are free to drop).
2. Odd integers (mode 2), both signs, k = 3..7: the numbers of solutions of x_1...x_k + eps = 2 prod (x_i - 1) in
   odd integers 3 <= x_1 < ... < x_k must be 1, 1, 2, 8, 47 (eps = -1) and 1, 1, 2, 4, 18 (eps = +1), as found by
   the PARI/GP program of pseudo/ (Theorem 9.3).
   In 1 and 2 the run is repeated with every divisor sent to the trial division, with every divisor sent to the
   sums, and with the arithmetic for quantities beyond 128 bits used throughout; the sets of completions (those
   found by scan3 plus those found by factoring the deferred cases) must coincide.
3. Eight primes, n + 1 = 2 phi(n), 3 | n: for 400 random admissible values of p_6 under random prefixes, and for
   the admissible p_6 in three ranges under the prefix 3, 5, 17, 257, 65537 (near 2^32, where N is factored; near
   a value with a completion in integers; around 2^33), the completions found by scan3, together with those found
   by factoring N for the cases it defers, must coincide with those found by factoring N for every pair.
4. Thirteen odd integers prime to 3 (mode 1), both signs: for 600 values of x_11 in the tree of
   pseudo/integer_tree_scan.py, 270 of them at nine places of the interval of the node with the longest interval
   and 330 under random nodes, the completions found by scan3 with the parameters of that run, together with those
   found by factoring N for the cases it defers, must coincide with those found by factoring N for every x_11.
usage: test_scan3.py"""
import sys, os, random, time, json
from math import prod
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, HERE)
import lastthree as L
from sympy import primefactors
from common import build, run_scan3, run_gp, line0, check_completion, sifted as passes

KNOWN = {255, 65535, 83623935, 4294967295, 6992962672132095}
P_SMALL = (1.0, 0.11, 1e9)          # deferral threshold of one second per x, to keep the forced runs finite


def all_completions(lines, eps, force):
    tot, comps, defs = run_scan3(lines, P_SMALL + (force,))
    g, _, _ = run_gp(defs, eps)
    allc = set(comps) | {c[:-2] for c in g}
    for c in allc: assert check_completion(c, eps), c
    return allc, tot, len(defs)


def int_nodes(k, eps):
    out = []
    def rec(xs, A, B):
        j = len(xs); m = k - j
        if A >= 2 * B: return
        pj = xs[-1] if xs else 1
        lo, hi = L.interval(A, B, pj, m, 2, 1, eps); lo = max(lo, pj + 1, 3)
        if hi < lo: return
        R0 = sorted({r for x in xs for r in primefactors(x - 1) if r > 2}); R1 = sorted({r for x in xs for r in primefactors(x)})
        if m == 3: out.append((xs, lo, hi, R0, R1)); return
        x = lo | 1
        while x <= hi:
            if all(x % r for r in R0) and all(x % r != 1 for r in R1): rec(xs + (x,), A * x, B * (x - 1))
            x += 2
    rec((), 1, 1)
    return out


def main():
    build(); t0 = time.time(); ok = True
    print("1. prime entries, n + 1 = 2 phi(n), p_1 >= 3")
    for k in range(3, 8):
        lines = [line0(+1, c, lo, hi) for c, A, B, lo, hi in L.frontier(k, 3, 2, 1, +1, 3)]
        forces = (0, 1, 2, 3) if k <= 6 else (0, 2, 3)
        res = [all_completions(lines, +1, f) for f in forces]
        sets = [{c for c in r[0] if passes(c)} for r in res]
        primes = sorted(prod(c) for c in sets[0] if all(L.proved_prime(x) for x in c))
        same = all(x == sets[0] for x in sets)
        good = same and set(primes) == {n for n in KNOWN if len(primefactors(n)) == k}
        ok &= good
        print(f"   k={k}: {len(lines)} prefixes, completions in integers {[len(r[0]) for r in res]}, of which "
              f"{len(sets[0])} pass the prime conditions, prime ones {primes}, "
              f"routes {forces} agree: {same}, deferred {[r[2] for r in res]}  {'ok' if good else 'FAIL'}", flush=True)
    print("2. odd integers, entry 3 allowed")
    expect = {-1: [1, 1, 2, 8, 47], +1: [1, 1, 2, 4, 18]}
    for eps in (-1, +1):
        for k in range(3, 8):
            nd = int_nodes(k, eps)
            lines = [f"{eps} 2 {len(xs)} {' '.join(map(str, xs))} {lo} {hi} {len(R0)} {' '.join(map(str, R0))} "
                     f"{len(R1)} {' '.join(map(str, R1))}" for xs, lo, hi, R0, R1 in nd]
            forces = (0, 1, 2, 3) if k <= 6 else (0, 2, 3)
            res = [all_completions(lines, eps, f) for f in forces]
            sets = [r[0] for r in res]
            same = all(s == sets[0] for s in sets)
            good = same and len(sets[0]) == expect[eps][k - 3]
            ok &= good
            print(f"   eps={eps:+d} k={k}: {len(nd)} nodes, {len(sets[0])} solutions (expected {expect[eps][k-3]}), "
                  f"routes {forces} agree: {same}, deferred {[r[2] for r in res]}  {'ok' if good else 'FAIL'}", flush=True)
    print("3. eight primes, 3 | n: scan3 against complete factorisation")
    fr = [x for x in L.frontier(8, 3, 2, 1, +1, 3) if 3 in x[0]]
    random.seed(8)
    pairs = []
    while len(pairs) < 400:
        c, A, B, lo, hi = random.choice(fr)
        s = random.randint(lo, hi)
        ss = L.primes_in(s, min(hi, s + 2000))
        ss = [int(x) for x in ss if all(int(x) % q != 1 for q in c)]
        if ss: pairs.append((c, ss[0]))
    n0 = (3, 5, 17, 257, 65537)
    s0 = 4596195557          # a completion in integers found in a trial run: p = 65533391633, q composite
    for a, b in ((2**32 + 1, 2**32 + 40000), (s0 - 30000, s0 + 30000), (2**33 - 30000, 2**33 + 30000)):
        pairs += [(n0, int(x)) for x in L.primes_in(a, b) if all(int(x) % q != 1 for q in n0)]
    lines = [line0(+1, c, s, s) for c, s in pairs]
    tot, comps, defs = run_scan3(lines)
    g, _, _ = run_gp(defs, +1)
    mine = set(comps) | {x[:-2] for x in g}
    full, dmax, sec = run_gp([tuple(c) + (s,) for c, s in pairs], +1)
    ref = {x[:-2] for x in full}
    good = mine == ref
    ok &= good
    print(f"   {len(pairs)} pairs (prefix, p_6): scan3 treated {int(tot['nx'])}, deferred {len(defs)}; "
          f"completions {len(mine)} (scan3 + factoring of the deferred) vs {len(ref)} (factoring all, "
          f"N up to {dmax} digits)  {'ok' if good else 'FAIL'}")
    for x in sorted(ref): print("     completion", x)
    print("4. thirteen odd integers prime to 3: scan3 against complete factorisation")
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), "pseudo"))
    import integer_tree as IT, integer_tree_scan as ITS
    from tail3lib import odd_primes_of
    for eps in (-1, +1):
        nodes, _ = IT.depth_k3_nodes(13, eps)
        def adm(xs, x):
            return x % 2 and x % 3 and all(x % r for r in odd_primes_of([y - 1 for y in xs])) and \
                all(x % r != 1 for r in odd_primes_of(list(xs)))
        xs0, lo0, hi0 = max(nodes, key=lambda n: n[2] - n[1])
        pairs = []
        for off in (3e6, 5e6, 1e7, 3e7, 1e8, 3e8, 1e9, 3e9, 1e10):
            x = lo0 + int(off); n = 0
            while n < 30:
                if adm(xs0, x): pairs.append((xs0, x)); n += 1
                x += 1
        random.seed(13 + eps)
        while len(pairs) < 600:
            xs, lo, hi = random.choice(nodes)
            x = random.randint(lo, hi)
            y = next((y for y in range(x, min(hi, x + 1000) + 1) if adm(xs, y)), None)
            if y: pairs.append((xs, y))
        tot, comps, defs = run_scan3([ITS.line1(eps, xs, x, x) for xs, x in pairs], ITS.PARAMS)
        g, _, _ = run_gp(defs, eps)
        mine = {c for c in set(comps) | {x[:-2] for x in g} if c[-1] % 3 and c[-2] % 3}
        full, dmax, sec = run_gp([tuple(xs) + (x,) for xs, x in pairs], eps)
        ref = {x[:-2] for x in full if x[-3] % 3 and x[-4] % 3}
        good = mine == ref
        ok &= good
        print(f"   eps={eps:+d}: {len(pairs)} values of x_11, scan3 treated {int(tot['nx'])}, deferred {len(defs)}; "
              f"completions prime to 3 {len(mine)} vs {len(ref)} (factoring all, N up to {dmax} digits, "
              f"{len({x[:-2] for x in full})} completions in integers)  {'ok' if good else 'FAIL'}", flush=True)
    print(f"all tests {'passed' if ok else 'FAILED'}  ({time.time() - t0:.0f}s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
