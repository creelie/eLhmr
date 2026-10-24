"""Exact one-candidate reduction; no claim of solving Lehmer's conjecture.

For a nonempty set S of distinct odd primes put A=prod(S), B=prod(p-1).
Any prime q>max(S) with A*q+eps=M*B*(q-1) has M=ceil(A/B).
Candidate construction uses integers only. Trial division is deliberately used
for primality here: positive certificates do not rely on probable primes.
"""
from dataclasses import dataclass, asdict
from itertools import combinations
from math import isqrt, prod, gcd
import json
from pathlib import Path

def prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n)+1, 2))

@dataclass(frozen=True)
class Candidate:
    prefix: tuple
    eps: int
    A: int
    B: int
    M: int
    D: int
    q: int | None

def candidate(prefix, eps=-1):
    s = tuple(sorted(prefix))
    if not s or len(s) != len(set(s)) or any(p % 2 == 0 or not prime(p) for p in s):
        raise ValueError('prefix must be a nonempty set of distinct odd primes')
    if eps not in (-1, 1):
        raise ValueError('eps must be -1 or +1')
    A, B = prod(s), prod(p-1 for p in s)
    M = (A+B-1)//B
    D = M*B-A
    assert 0 < D < B
    q = 1+(A+eps)//D if (A+eps) % D == 0 else None
    return Candidate(s, eps, A, B, M, D, q)

def certified_solution(prefix, eps=-1):
    c = candidate(prefix, eps)
    if c.q is None or c.q <= max(c.prefix) or not prime(c.q):
        return None
    n = c.A*c.q
    assert n+eps == c.M*c.B*(c.q-1)
    return n

def verify():
    ps = [p for p in range(3, 48, 2) if prime(p)]
    qs = [q for q in range(3, 258, 2) if prime(q)]
    prefixes, comparisons, hits = 0, 0, []
    for k in range(1, 7):
        for s in combinations(ps, k):
            prefixes += 1
            A, B, r = prod(s), prod(p-1 for p in s), max(s)
            # Bound used in the written proof, checked independently here.
            assert 2*A <= r*B
            for eps in (-1, 1):
                c = candidate(s, eps)
                for q in qs:
                    if q <= r:
                        continue
                    comparisons += 1
                    M, rem = divmod(A*q+eps, B*(q-1))
                    direct = rem == 0
                    reduced = c.q == q
                    assert direct == reduced
                    if direct:
                        assert M == c.M
                        assert gcd(c.D, M*A*B) == 1
                        assert 2*c.D <= B
                        if eps == -1:
                            assert 2*c.D < B and c.D >= 3
                        hits.append({'prefix':s, 'eps':eps, 'q':q, 'M':M})
    known = [15, 255, 65535, 83623935, 4294967295, 6992962672132095]
    prefixes_known = [(3,), (3,5), (3,5,17), (3,5,17,353),
                      (3,5,17,257), (3,5,17,353,929)]
    for s, n in zip(prefixes_known, known):
        assert certified_solution(s, 1) == n
    # Negative control: this is an integer completion, but its last entry is
    # composite. The exact equation and rounding alone must not certify it.
    fermat = (3,5,17,257,65537)
    c = candidate(fermat, 1)
    assert c.q == 2**32+1 == 641*6700417
    assert c.A*c.q+1 == c.M*c.B*(c.q-1)
    assert certified_solution(fermat, 1) is None
    return {'prefixes':prefixes, 'prime_tail_comparisons_both_signs':comparisons,
            'hits':hits, 'known_companion_positive_controls':len(known),
            'composite_tail_negative_control':asdict(c),
            'status':'PASS',
            'scope':'finite consistency tests; general proof is in the manuscript; full conjecture remains open'}

if __name__ == '__main__':
    r = verify()
    out = Path(__file__).resolve().parent/'verification'/'single-candidate.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ('hits','composite_tail_negative_control')}))
