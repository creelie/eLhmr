# Section 6.5 of the paper: the bound (6.6) for P_k when (H1) holds for all j <= k-1, the first J prime factors having
# product of p/(p-1) below Vstar by Proposition 2.5.  Usage: python3 ratio_bound.py [K]   (default K = 16000)
#
# l_i is a lower bound for the i-th smallest prime factor, rho_i the least integer x with x^i >= 2^(2^(i-s)), and
# w_i = max(l_i, rho_i).  For J < i <= k-1 we have p_i >= w_i, and p_k >= max(l_k, w_{k-1} + 2), so
#   P_k < Vstar * max{ 1, max_{J <= i < i0} (w'_i + 2)/(w'_i + 1) prod_{J < l <= i} w_l/(w_l - 1),
#                     (1 + 16/(rho_i0 - 2)) prod_{J < l < i0} w_l/(w_l - 1) },   w'_i = max(w_i, l_{i+1} - 2),
# with i0 the least i >= max(J + 1, s + 4) with rho_i > 10^30 (tail estimate of Lemma 6.13).
# Here an integer lower bound for rho_i is used in place of rho_i, which can only enlarge the bound.
import sys
import mpmath
import sympy
from fractions import Fraction

mpmath.mp.dps = 80


def rho_low(i, s):
    """an integer <= rho_i = ceil(2^(2^(i-s)/i)) (1 for i < s)."""
    if i < s:
        return 1
    e = mpmath.mpf(2) ** (i - s) / i
    if e > 400:
        return 10 ** 100
    return max(1, int(mpmath.floor(mpmath.power(2, e) * (1 - mpmath.mpf(10) ** -60))))


def R(s, ell, J, Vstar):
    best = Fraction(Vstar)                     # k <= J
    prod = Fraction(Vstar)
    wprev = max(ell(J), rho_low(J, s))         # p_J >= w_J when k >= J + 1
    i = J + 1
    while True:
        wk = max(ell(i), wprev + 2)            # k = i
        best = max(best, prod * Fraction(wk, wk - 1))
        w = max(ell(i), rho_low(i, s))
        if w > 10 ** 30 and i >= s + 4:
            return max(best, prod * (1 + Fraction(16, w - 2)))
        prod *= Fraction(w, w - 1)
        wprev = w
        i += 1


K = int(sys.argv[1]) if len(sys.argv) > 1 else 16000
r = list(sympy.primerange(5, 4 * 10 ** 6))          # r_i, the primes from 5 on
ell2 = lambda i: r[i - 1]
V2 = Fraction(2999999, 1000000)
s = K - 40
assert R(s, ell2, K, V2) < 3
while R(s + 1, ell2, K, V2) < 3:
    s += 1
print(f"(ii) M >= 3, 3 not dividing n, J = {K}, Vstar = 2.999999: largest s with R_s < 3 is s = {s};",
      f"R_s = {float(R(s, ell2, K, V2)):.12f}, R_(s+1) = {float(R(s + 1, ell2, K, V2)):.12f}")
for t in (s, s + 1):
    print(f"     s = {t}: rho_J >= {rho_low(K, t)}, rho_(J+1) >= {rho_low(K + 1, t)}, l_J = {ell2(K)}, l_(J+1) = {ell2(K + 1)}")

# (iii) 3 | n: the first J = 10^8 + 1 prime factors are 3 and 10^8 primes = 2 mod 3, with product below
# (3/2)(8/3)(1 - 10^-6); the i-th prime factor is at least the i-th odd prime, so at least 2i + 1.
J3 = 10 ** 8 + 1
V3 = Fraction(3, 2) * Fraction(333333, 125000)
ell3 = lambda i: 2 * i + 1
print(f"(iii) 3 | n, J = 10^8 + 1, Vstar = 4(1 - 10^-6): R_s for s = 10^8 is {float(R(10 ** 8, ell3, J3, V3)):.12f}",
      "< 4" if R(10 ** 8, ell3, J3, V3) < 4 else ">= 4")
