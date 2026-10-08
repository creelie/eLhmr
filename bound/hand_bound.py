"""Exact check of the numbers in the proof of Proposition 6.11 (no composite solution of
phi(n) | n-1 is 2-heavy) and of the remark after it (none is 1-heavy).

For each case the lower bounds b_i for the i-th smallest prime factor are the i-th element of
the list of primes allowed in that case, raised where condition (H1) forces
p_i >= theta_i^(1/i) with theta_i = 2^(2^(i-s)).  The program prints beta_j = prod_{i<=j} b_i/(b_i-1),
the bound beta_j * b_j/(b_j-1) for P_k when k = j+1, and the tail bound.
"""
from fractions import Fraction as F
import math

from sympy import integer_nthroot, isprime, nextprime


def h1_bound(i, s):
    t = 2 ** (2 ** (i - s)) if i >= s else 1
    r, exact = integer_nthroot(t, i)
    return r if exact else r + 1


def lower_bounds(first, allowed, s, depth):
    b = list(first)
    while len(b) < depth:
        i = len(b) + 1
        q = max(b[-1] + 1, h1_bound(i, s))
        q = q if isprime(q) else nextprime(q)
        while not allowed(q):
            q = nextprime(q)
        b.append(q)
    return b


def report(name, first, allowed, s, M, depth, tail_from, tail):
    b = lower_bounds(first, allowed, s, depth)
    beta, worst = F(1), F(0)
    print("%s (s = %d, M >= %d): b = %s" % (name, s, M, b))
    for j, bj in enumerate(b, 1):
        beta *= F(bj, bj - 1)
        worst = max(worst, beta * F(bj, bj - 1))
        print("   j = %d  b_j = %d  beta_j = %.6f  beta_j*f(b_j) = %.6f" % (j, bj, beta, beta * F(bj, bj - 1)))
    big = float(beta) * math.exp(2 * tail)
    print("   k >= %d: P_k < beta_%d * exp(%.4f) = %.6f" % (tail_from, depth, 2 * tail, big))
    total = max(float(worst), big)
    print("   bound for P_k: %.6f, less than M: %s\n" % (total, total < M))


# s = 2: tail over 8 <= i <= k-1, with p_8 >= 257, p_9 > 19000 and p_i > 4^i for i >= 10
print("p_i >= theta_i^(1/i) for s = 2:", [h1_bound(i, 2) for i in range(1, 11)])
tail2 = 1 / 256 + 1 / 19000 + sum(1 / (4 ** i - 1) for i in range(10, 80))
print("tail sum for s = 2: %.7f < 0.004: %s\n" % (tail2, tail2 < 0.004))
T = 0.004
report("(a) p1 = 3", [3, 5, 7, 11, 13, 17], lambda q: True, 2, 4, 7, 9, T)
report("(b) p1 = 5, p2 = 7", [5, 7], lambda q: q % 5 != 1 and q % 7 != 1, 2, 2, 7, 9, T)
report("(c) p1 = 5, p2 != 7", [5, 13], lambda q: q % 5 != 1, 2, 2, 7, 9, T)
report("(d) p1 >= 7", [7], lambda q: True, 2, 2, 7, 9, T)

# s = 1: p_6 >= 41, p_7 >= 569, p_8 >= 65537; tail over 9 <= i <= k-1, where
# p_i >= 2^(2^(i-1)/i) > 4^i because 2^(i-1) > 2i^2 for i >= 9
print("p_i >= theta_i^(1/i) for s = 1:", [h1_bound(i, 1) for i in range(1, 10)])
tail1 = sum(1 / (4 ** i - 1) for i in range(9, 80))
report("p1 = 3", [3, 5, 7, 11, 13], lambda q: True, 1, 4, 8, 10, tail1)
report("p1 >= 5", [5], lambda q: True, 1, 2, 8, 10, tail1)
