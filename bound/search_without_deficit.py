"""Exact search behind the bound n < 2^(2^(k-s)) for Lehmer numbers.

Let n = p_1 ... p_k (p_1 < ... < p_k odd primes) with n - 1 = M phi(n).
Write P_j = p_1...p_j, F_j = (p_1-1)...(p_j-1), r_j = P_j/F_j.
Known facts used (Lemmas 2.1, 2.2 and 6.1 of the paper):
  (C) p does not divide q - 1 for p, q | n;
  (R) r_j < M for j < k, and r_k = M + 1/phi(n) > M;
  (T) if 3 | n then M = 1 (mod 3), so M >= 4; in all cases M >= 2;
  (L) p_k = (M F_{k-1} - 1)/(M F_{k-1} - P_{k-1}).
Claim checked: no such n satisfies
  (P) P_j >= 2^(2^(j-s)) for every s <= j <= k-1.
The search runs over prefixes p_1..p_j satisfying (C), (P) and r_j < M,
prunes a prefix when an upper bound for r_k over all extensions is <= the
least admissible M, and tests (L) exactly at every prefix.
All arithmetic is exact (integers and Fractions).
"""
import sys
from fractions import Fraction
import gmpy2
import sympy

s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
BIG = 10**30
LIMIT = 2 * 10**7
PR = list(sympy.primerange(3, LIMIT))
IDX = {p: i for i, p in enumerate(PR)}
stats = {"nodes": 0, "maxdepth": 0, "lasttests": 0}
found = []


def thr(i):
    """(P) asks P_i >= thr(i); it binds only for i >= s."""
    return 1 << (1 << (i - s)) if i >= s else 1


def prime_after(p, m):
    """Lower bound for the m-th odd prime greater than p (m >= 1)."""
    if p < 3:
        return PR[m - 1]
    if p in IDX and IDX[p] + m < len(PR):
        return PR[IDX[p] + m]
    return p + 2 * m


def min_root(P, e, T):
    """Least integer m >= 1 with P * m^e >= T."""
    if P >= T:
        return 1
    q = -(-T // P)
    m = int(gmpy2.iroot(gmpy2.mpz(q), e)[0])
    if m ** e < q:
        m += 1
    return m


def ext_bound(j, P, last, first):
    """Upper bound for prod_{i=j+1}^{k} p_i/(p_i-1), over every k >= j+1 and
    every extension p_{j+1} < ... < p_k of the prefix (length j, product P,
    largest prime last) with p_{j+1} >= first and (P) for j < i <= k-1.

    For j < i <= k-1:  p_i >= b_i = max(i-th prime bound, root bound), where
      the root bound uses P_i <= P * p_i^(i-j) and P_i >= thr(i);
    p_k >= b_{k-1} + 2  (or p_k >= first when k = j+1)."""
    best = Fraction(first, first - 1)          # k = j+1
    prod = Fraction(1)
    i = j + 1
    while True:
        root = min_root(P, i - j, thr(i))
        b = max(first if i == j + 1 else prime_after(first, i - j - 1), root)
        if root > BIG and i >= j + 3:
            # rho_{i+1} >= rho_i^(4/3) here, so sum_{i' >= i} 1/(b_i' - 1) <= 2/(root-1)
            # and prod_{i' >= i} (b_i'/(b_i'-1))^2 <= exp(4/(root-1)) <= 1 + 16/(root-2)
            return max(best, prod * (1 + Fraction(16, root - 2)))
        prod *= Fraction(b, b - 1)
        best = max(best, prod * Fraction(b + 2, b + 1))   # k = i+1
        i += 1


def m_need(S, ratio):
    lo = ratio.numerator // ratio.denominator + 1       # M > r_j
    if S and S[0] == 3:
        m = max(4, lo)
        while m % 3 != 1:
            m += 1
        return m
    return max(2, lo)


def admissible(S, q):
    return all((q - 1) % p for p in S)


def dfs(S, P, F):
    j = len(S)
    ratio = Fraction(P, F)
    need = m_need(S, ratio)
    last = S[-1] if S else 1
    first = prime_after(last, 1)
    if ratio * ext_bound(j, P, last, first) <= need:
        return
    stats["nodes"] += 1
    stats["maxdepth"] = max(stats["maxdepth"], j)
    # (L): S = p_1..p_{k-1}, last prime determined by M
    if j >= 1:
        top = ratio * Fraction(last + 2, last + 1)          # r_k < this
        M = need
        while M < top:
            if not (S[0] == 3 and M % 3 != 1):
                stats["lasttests"] += 1
                D = M * F - P
                if (M * F - 1) % D == 0:
                    qk = (M * F - 1) // D
                    if qk > last and gmpy2.is_prime(qk) and admissible(S, qk):
                        found.append((S + [qk], M))
                        print("LEHMER", S + [qk], M, flush=True)
            M += 1
    # children: p_{j+1} = q as a non-last prime, so (P) applies at j+1
    q = first
    lo = -(-thr(j + 1) // P)
    if lo > q:
        q = int(gmpy2.next_prime(lo - 1))
    while True:
        # bound valid for every extension with p_{j+1} >= q; decreasing in q
        if ratio * ext_bound(j, P, last, q) <= need:
            break
        if admissible(S, q):
            dfs(S + [q], P * q, F * (q - 1))
        q = int(gmpy2.next_prime(q))


dfs([], 1, 1)
print("s =", s, "nodes", stats["nodes"], "maxdepth", stats["maxdepth"],
      "last-prime tests", stats["lasttests"], "Lehmer numbers found", len(found), flush=True)
