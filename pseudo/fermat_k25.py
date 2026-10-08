#!/usr/bin/env python3
"""For the 25-entry tuple of Theorem 9.5 (companion_k25.txt), with A the product of its entries (A + 1 = 2B):
for every entry x, whether 2^(A+1) = 1 (mod x), which holds whenever lambda(x) divides A + 1, in particular
when x is prime; for the entries below 10^13 also the factorisation, whether x is squarefree, and whether
q - 1 divides A + 1 for every prime q dividing x."""
import sys
import gmpy2
from sympy import factorint
sys.set_int_max_str_digits(0)

x = [int(t) for t in open(sys.argv[1] if len(sys.argv) > 1 else "companion_k25.txt").read().split()]
A = gmpy2.mpz(1)
for t in x: A *= t
B = gmpy2.mpz(1)
for t in x: B *= t - 1
assert A + 1 == 2 * B
E = A + 1
print(f"{len(x)} entries, A + 1 = 2B, A has {len(str(A))} digits")
for i, t in enumerate(x, 1):
    t = gmpy2.mpz(t)
    prp = gmpy2.is_prime(t, 30)
    ferm = gmpy2.powmod(2, E, t) == 1
    line = f"x_{i:<2d} {int(t).bit_length():6d} bits  {'probable prime' if prp else 'composite':14s}  2^(A+1) = 1 mod x: {'yes' if ferm else 'no'}"
    if t < 10 ** 13:
        f = factorint(int(t))
        sq = all(e == 1 for e in f.values())
        kor = [q for q in f if E % (q - 1)]
        line += f"  factors {f}  squarefree: {'yes' if sq else 'no'}  primes q with q-1 not dividing A+1: {kor}"
    print(line, flush=True)
