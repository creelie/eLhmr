#!/usr/bin/env python3
"""One- and two-prime extensions of the known solutions of n + 1 = 2 phi(n) (Theorem 1.6 of the paper).
A one-prime extension of n0 is n0*q with q = n0 + 2 prime; a two-prime extension is n0*p*q with
(p - n0 - 1)(q - n0 - 1) = n0^2 + n0 + 1.  Runtime: seconds."""
from sympy import factorint, isprime, divisors, primefactors
known = [1, 3, 15, 255, 65535, 83623935, 4294967295, 6992962672132095]
def phi(n):
    r = 1
    for p in primefactors(n): r *= p - 1
    return r
for n0 in known:
    assert n0 == 1 or 2 * phi(n0) == n0 + 1
    N = n0 * n0 + n0 + 1; f = factorint(N)
    two = []
    for d in divisors(N):
        e = N // d
        if d > e: break
        p, q = n0 + 1 + d, n0 + 1 + e
        if isprime(p) and isprime(q):
            n = n0 * p * q; assert 2 * phi(n) == n + 1; two.append((p, q, n))
    print(f"n0 = {n0}: n0+2 prime: {isprime(n0+2)};  n0^2+n0+1 = {N} = {f};  two-prime extensions: {two}")
