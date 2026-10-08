"""Exact search of Section 6.3 of the paper (the tree T_s, rules R1-R4), behind the
bound n < 2^(2^(k-s)) for Lehmer numbers (Theorem 1.2).  Usage: python3 search.py 7

Let n = p_1 ... p_k (p_1 < ... < p_k odd primes) with n - 1 = M phi(n).
Write P_j = p_1...p_j, F_j = (p_1-1)...(p_j-1) = phi(P_j), r_j = P_j/F_j, and
t_i = 2^(2^(i-s)) for i >= s, t_i = 1 for i < s.  (In the paper these are A_j, B_j, P_j
and theta_i, and B_j(q) below is Gamma_j(q).)  Facts used (Lemmas 2.1, 2.2 and 6.1):
  (C) p does not divide q - 1 for p, q | n;
  (R) r_j < M for j < k, and r_k = M + 1/phi(n) > M;
  (T) if 3 | n then M = 1 (mod 3), so M >= 4; in all cases M >= 2;
  (L) p_k = (M F_{k-1} - 1)/(M F_{k-1} - P_{k-1}).
A Lehmer number is s-heavy if P_j >= t_j (H1) and V_j >= t_{j+1} (H2) for all
j <= k-1, where V_j = M F_j (P_j + 1)/(M F_j - P_j).  The search visits every
prefix of an s-heavy Lehmer number (Proposition 6.14):
  R1  ratio test: discard the prefix if r_j * B_j(q_1) <= mu, the least admissible M;
  R2  deficit test: discard the prefix if V_j(mu) < t_{j+1};
  R3  last prime: test (L) for every admissible M in [mu, r_j (p_j+2)/(p_j+1));
  R4  children q > p_j with P_j q >= t_{j+1}, omitting (i) q once r_j B_j(q) <= mu,
      (ii) the primes q <= q_c when r_j B_j(q) <= the next admissible M,
      (iii) q > q_c with V_{j+1}(mu) < t_{j+2} (an interval, from a quadratic).
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
stats = {"nodes": 0, "maxdepth": 0, "lasttests": 0, "light": 0}
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
    # deficit form of Nielsen's lemma: n < V^(2^(k-j-1)), V = M F (P+1)/(M F - P),
    # decreasing in M, so M = need gives a valid bound; light prefix if V < 2^(2^(j+1-s))
    if j + 1 >= s:
        V = Fraction(need * F * (P + 1), need * F - P)
        if V < (1 << (1 << (j + 1 - s))):
            stats["light"] += 1
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
    q0 = first
    lo = -(-thr(j + 1) // P)
    if lo > q0:
        q0 = int(gmpy2.next_prime(lo - 1))
    D = need * F - P                      # > 0 since need > r_j
    qc = (need * F) // D                  # q <= qc: r_{j+1} >= need (child needs a larger M)
    # heavy test at the child with M = need (valid upper bound for V since V decreases in M):
    # V(q) = M F (q-1)(P q + 1)/(D q - M F) >= T  <=>  Q(q) >= 0 for q > M F / D
    segments = []
    if j + 2 >= s:
        T = 1 << (1 << (j + 2 - s))
        MF = need * F
        A2 = MF * P
        B1 = MF - MF * P - T * D
        C0 = T * MF - MF
        disc = B1 * B1 - 4 * A2 * C0
        if disc < 0:
            segments = [(q0, None)]
        else:
            sq = int(gmpy2.isqrt(disc))
            qm = (-B1 - sq) // (2 * A2) + 1     # Q >= 0 for q <= roots[0]; take a safe margin
            qp = (-B1 + sq) // (2 * A2) - 1
            # q <= qc (child with larger M), q in (qc, qm] and q >= qp are candidates; margins keep it safe
            end1 = max(qc, qm) + 1
            segments = [(q0, end1), (max(q0, qp, end1 + 1), None)]
    else:
        segments = [(q0, None)]
    # Region q <= qc: there r_{j+1} >= need, so the child needs the next admissible M.
    # The bound ratio*ext_bound(j, P, last, q) decreases in q, so one test at the start
    # of the region against that M settles the whole region when it fails.
    need2 = need + 1
    if S and S[0] == 3:
        while need2 % 3 != 1:
            need2 += 1
    for (a_, b_) in segments:
        q = a_ if gmpy2.is_prime(a_) else int(gmpy2.next_prime(a_))
        while True:
            if b_ is not None and q > b_:
                break
            if q <= qc and ratio * ext_bound(j, P, last, q) <= need2:
                # every q' in [q, qc] is dead; jump past qc
                q = int(gmpy2.next_prime(qc))
                continue
            if ratio * ext_bound(j, P, last, q) <= need:
                break
            if admissible(S, q):
                dfs(S + [q], P * q, F * (q - 1))
            q = int(gmpy2.next_prime(q))

dfs([], 1, 1)
print("s =", s, "nodes", stats["nodes"], "maxdepth", stats["maxdepth"],
      "last-prime tests", stats["lasttests"], "light", stats["light"], "Lehmer numbers found", len(found), flush=True)
