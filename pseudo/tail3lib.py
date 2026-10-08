#!/usr/bin/env python3
"""Shared driver for the C program tail3 (build it with  gcc -O2 -o tail3 tail3.c -lgmp -lm  in this directory).

A task is a prefix x_1 < ... < x_j (j = k-3) with the exact interval [lo, hi] for t = x_{k-2}.  tail3 runs t over
[lo, hi] (primes in mode 0; admissible odd integers in modes 2/3) and returns every integer completion (t, p, q),
t < p < q, of  A t p q + eps = 2 B (t-1)(p-1)(q-1)  (A = prod x_i, B = prod (x_i - 1)).  Deferred problems (F lines)
are solved here by a complete factorisation of N with every prime factor proved prime (lastthree.factor_proved).
Every completion is re-checked by exact integer arithmetic."""
import sys, subprocess, time, os
from math import prod
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import lastthree as L
from sympy import primefactors

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "tail3")

def odd_primes_of(ns):
    s = set()
    for n in ns:
        if n > 1:
            fs = primefactors(n)
            m = n
            for f in fs:
                while m % f == 0: m //= f
            assert m == 1
            s.update(fs)
    return sorted(x for x in s if x > 2)

def line_for(chosen, lo, hi, eps, mode, extra0=()):
    """mode 0: t prime.  mode 2: t admissible odd integer.  mode 3: as 2, and 3-divisible p, q reported as D."""
    base = f"2 1 {eps} {len(chosen)} {' '.join(map(str, chosen))} {lo} {hi} {mode}"
    if mode < 2: return base
    R0 = sorted(set(odd_primes_of([x - 1 for x in chosen])) | set(extra0))   # t != 0 mod r   (gcd(t, x_i - 1) = 1)
    R1 = odd_primes_of(list(chosen))                                          # t != 1 mod r   (gcd(x_i, t - 1) = 1)
    return base + f" {len(R0)} {' '.join(map(str, R0))} {len(R1)} {' '.join(map(str, R1))}"

def factored_completions(tup, eps, a=2, b=1):
    t = tup[-1]; A = prod(tup); B = prod(x - 1 for x in tup)
    C = a * B - b * A; N = b * (a * A * B + eps * C); aB = a * B
    divs = [1]
    for p, e in L.factor_proved(N): divs = [d * p ** i for d in divs for i in range(e + 1)]
    out = []
    for e in divs:
        if e * e >= N or (e + aB) % C or (N // e + aB) % C: continue
        p, q = (e + aB) // C, (N // e + aB) // C
        if p > t and q > p: out.append((p, q))
    return out

def run(lines, eps, timeout=None):
    """returns (totals dict, list of completions (tuple, tag)) ; tag 'S' or 'D' (3 | p or q)."""
    t0 = time.time()
    p = subprocess.run([BIN], input="\n".join(lines) + "\n", capture_output=True, text=True, timeout=timeout)
    tot = dict(tasks=0, nt=0, single=0, surv=0, multi=0, work=0, S=0, D=0, deferred=0, cpu=0.0)
    comps = []
    for l in p.stdout.splitlines():
        if l.startswith("T"):
            v = l.split()[1:]
            tot['tasks'] += 1; tot['nt'] += int(v[0]); tot['single'] += int(v[1]); tot['surv'] += int(v[2])
            tot['multi'] += int(v[3]); tot['work'] += int(float(v[4])); tot['S'] += int(v[5]); tot['cpu'] += float(v[6])
            tot['deferred'] += int(v[7]); tot['D'] += int(v[8]) if len(v) > 8 else 0
        elif l[0] in "SD":
            comps.append((tuple(int(x) for x in l.split()[1:]), l[0]))
        elif l.startswith("F"):
            tup = tuple(int(x) for x in l.split()[1:])
            for pq in factored_completions(tup, eps):
                comps.append((tup + pq, 'Fs'))
    assert tot['tasks'] == len(lines), (tot['tasks'], len(lines), p.stderr[:500])
    for tup, tag in comps:          # exact re-check
        X = prod(tup); Phi = prod(x - 1 for x in tup)
        assert X + eps == 2 * Phi, tup
        assert all(u < v for u, v in zip(tup, tup[1:])) and all(x % 2 for x in tup), tup
    tot['wall'] = round(time.time() - t0, 1)
    return tot, comps
