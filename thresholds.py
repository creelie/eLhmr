#!/usr/bin/env python3
"""Exact thresholds used in Section 2 of the paper (rational arithmetic).  Runtime: seconds."""
from fractions import Fraction as Fr
from math import prod
from sympy import primerange

r = list(primerange(5, 10**5))                                   # primes >= 5
q = [p for p in primerange(5, 10**7) if p % 3 == 2]              # primes >= 5, = 2 (mod 3)

# Lemma 2.2, eps = -1: if 3 | n then M = 1 (mod 3), M >= 4, and 4 < (3/2) prod_{i <= k-1} q_i/(q_i - 1).
P, k = Fr(3, 2), 1
while P <= 4:
    P *= Fr(q[k - 1], q[k - 1] - 1); k += 1
print("n - 1 = M phi(n), 3 | n:  omega(n) >=", k)

def first_k(primes, M):
    """least k with prod_{i<=k} p_i/(p_i-1) >= M - 1/prod_{i<=k}(p_i - 1)."""
    P, D = Fr(1), 1
    for k, p in enumerate(primes, 1):
        P *= Fr(p, p - 1); D *= p - 1
        if P >= M - Fr(1, D): return k

# Lemma 2.3: with 3 not dividing n, M = 2 as long as the product over the k smallest primes >= 5 stays below 3.
k3 = next(k for k in range(1, 200) if prod(Fr(p, p - 1) for p in r[:k]) > 3)
print("n - 1 = M phi(n), 3 not dividing n:  M >= 3 needs omega(n) >=", k3)
print("  product over the 14 smallest primes >= 5 =", float(prod(Fr(p, p - 1) for p in r[:14])))
print("  product over the 6 smallest primes >= 5 =", float(prod(Fr(p, p - 1) for p in r[:6])))
print("n + 1 = M phi(n), 3 not dividing n:  M >= 3 needs omega(n) >=", first_k(r, 3))
print("  product over the 32 smallest primes >= 5 =", float(prod(Fr(p, p - 1) for p in r[:32])))

# Theorem 1.5, 3 | n: M = 2 (mod 3), so M >= 5, and 5 - 1/phi(n) < n/phi(n) <= (3/2) prod_{i<=k-1} q_i/(q_i-1);
# since 5 - 1/phi(n) > 4, the threshold computed above for n - 1 = M phi(n) applies verbatim.
print("n + 1 = M phi(n), 3 | n, M >= 3:  omega(n) >=", k)

# Corollary 2.4: for omega(n) = k <= 7 (odd primes, any), M < prod_{k smallest odd primes} p/(p-1) + 1/prod (p-1).
odd = list(primerange(3, 20))
worst = max(prod(Fr(p, p - 1) for p in odd[:k]) + Fr(1, prod(p - 1 for p in odd[:k])) for k in range(2, 8))
print("n + 1 = M phi(n), 2 <= omega(n) <= 7:  M <", float(worst), "< 3, so M = 2")
