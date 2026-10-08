#!/usr/bin/env python3
"""
Third implementation of the three-prime completion: the sum of the two factors.  No lattice boxes, no
factoring, and no primality proof.

At a node (p_1, ..., p_{k-3}) and a prime s = p_{k-2}, put A' = A s, B' = B (s - 1), C = 2B' - A',
N = 2A'B' + eps C and r = -2B' mod C.  The last two primes p < q satisfy (C p - 2B')(C q - 2B') = N, so
t = C p - 2B' and t* = C q - 2B' are complementary divisors of N, both congruent to r modulo C, and
N = r^2 (mod C).  Write t = r + C u, t* = r + C v (0 <= u <= v).  Then

    C u v + r (u + v) = m := (N - r^2) / C,

so the sum S = u + v lies in the single class S = m r^{-1} (mod C), and u, v are the roots of
X^2 - S X + (m - r S)/C.  Divisors with u < u_d are tested by one division each.  For u >= u_d the sum
t + N/t = 2r + C S is at most t_d + N/t_d with t_d = r + C u_d, because x + N/x decreases on (0, sqrt N];
so S runs over at most N/(C^3 u_d) + 1 values of one residue class, and each needs one square test.
With u_d = floor(sqrt(N/C^3)) + 1 the work is about 2 (N/C^3)^(1/2) + 2 operations per s.

Every t found yields integers p = (t + 2B')/C and q = (N/t + 2B')/C with A' p q + eps = 2B'(p-1)(q-1),
whether or not p and q are prime; primality is looked at only afterwards, for reporting.  The primes s come
from a plain segmented sieve of Eratosthenes written for this file.
"""
import math
from gmpy2 import mpz, isqrt, isqrt_rem, invert, gcd
import gmpy2

class StatsC:
    def __init__(self): self.direct = 0; self.sums = 0; self.found = 0

def _base_primes(n):
    sieve = bytearray([1]) * (n + 1); sieve[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(n) + 1):
        if sieve[i]: sieve[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if sieve[i]]

def primes_between(lo, hi):
    """the primes p with lo <= p <= hi, by a segmented sieve."""
    lo = max(lo, 2)
    if hi < lo: return []
    seg = bytearray([1]) * (hi - lo + 1)
    for p in _base_primes(math.isqrt(hi)):
        start = max(p * p, ((lo + p - 1) // p) * p)
        if start > hi: continue
        seg[start - lo::p] = bytearray(len(range(start, hi + 1, p)))
    return [lo + i for i, f in enumerate(seg) if f]

def divisors_sum(N, c, r, stats=None):
    """all t with t | N, t = r (mod c) and 1 <= t <= sqrt(N), assuming gcd(r, c) = 1, c >= 2 and N = r^2 (mod c)."""
    N = mpz(N); c = mpz(c); r = mpz(r) % c
    assert c >= 2 and gcd(r, c) == 1 and (N - r * r) % c == 0
    sN = isqrt(N)
    if r > sN: return []
    U = (sN - r) // c                                   # t <= sqrt(N)  <=>  u <= U
    m = (N - r * r) // c
    S0 = (m * invert(r, c)) % c
    ud = min(U + 1, isqrt(N // (c * c * c)) + 1)        # u < ud: trial division
    out = []
    for u in range(int(ud)):
        t = r + c * u
        if N % t == 0: out.append(t)
    if stats: stats.direct += int(ud)
    if ud > U: return out
    td = r + c * ud
    Smax = (td + N // td - 2 * r) // c                  # 2r + cS = t + N/t <= td + N/td
    Smin = max(2 * ud, (2 * sN - 2 * r) // c)           # u, v >= ud, and t + N/t >= 2 sqrt(N)
    S = Smin + ((S0 - Smin) % c)
    n = 0
    while S <= Smax:
        n += 1
        P, rem = divmod(m - r * S, c)
        assert rem == 0
        D = S * S - 4 * P
        if D >= 0:
            d, rr = isqrt_rem(D)
            if rr == 0 and (S - d) % 2 == 0:
                u = (S - d) // 2
                if ud <= u <= U:
                    t = r + c * u
                    assert N % t == 0 and N // t == r + c * ((S + d) // 2)
                    out.append(t)
        S += c
    if stats: stats.sums += n
    return sorted(out)

def pairs_in_class(N, c, r, stats=None):
    """all t <= sqrt(N) with t | N and both t and N/t congruent to r modulo c (c >= 1).

    A common factor g of r and c divides t and N/t, so g^2 is split off first.  In the search gcd(r, c) = 1 and
    c is large, and this is divisors_sum; the general case is used only for the validation equations."""
    N = mpz(N); c = mpz(c); r = mpz(r) % c; scale = mpz(1)
    while c > 1:
        g = gcd(r, c)
        if g == 1: break
        if N % (g * g): return []
        N //= g * g; r //= g; c //= g; scale *= g
    if c == 1:                                          # every integer is in the class: trial division
        sN = isqrt(N)
        return [scale * t for t in range(1, int(sN) + 1) if N % t == 0]
    if (N - r * r) % c: return []                       # then t and N/t cannot both be = r (mod c)
    return [scale * t for t in divisors_sum(N, c, r, stats)]

def completions_c(chosen, A, B, a, b, eps, stats=None, cands=None):
    """all integers p < q with p > max(chosen) and b (A p q + eps) = a B (p-1)(q-1); those with p and q both
    probable primes are returned, the others appended to cands."""
    A = mpz(A); B = mpz(B)
    C = a * B - b * A
    if C <= 0: return []
    N = b * (a * A * B + eps * C)
    r = (-a * B) % C
    sols = []; pmax = max(chosen)
    for t in pairs_in_class(N, C, r, stats):
        p, e1 = divmod(t + a * B, C); q, e2 = divmod(N // t + a * B, C)
        assert e1 == 0 and e2 == 0
        if p <= pmax or q <= p: continue
        assert b * (A * p * q + eps) == a * B * (p - 1) * (q - 1)
        if stats: stats.found += 1
        if gmpy2.is_prime(p) and gmpy2.is_prime(q):
            sols.append((int(A * p * q), tuple(chosen) + (int(p), int(q))))
        elif cands is not None:
            cands.append((int(p), int(q)))
    return sols

def node_c(chosen, A, B, lo, hi, a, b, eps, stats=None, cands=None):
    """every admissible prime s in [lo, hi] as p_{k-2} after the prefix chosen, completed by completions_c."""
    ns = 0; sols = []
    for s in primes_between(lo, hi):
        if s <= max(chosen) or any(s % q == 1 for q in chosen): continue
        ns += 1
        sols += completions_c(chosen + (s,), A * s, B * (s - 1), a, b, eps, stats=stats, cands=cands)
    return ns, sols
