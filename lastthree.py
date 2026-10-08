#!/usr/bin/env python3
"""
The last three primes of a solution of  b (n + eps) = a phi(n),  n = p_1 ... p_k squarefree.

At depth k-3 the prefix p_1 < ... < p_{k-3} gives A = prod p_i, B = prod (p_i - 1), and the interval for the
next prime s = p_{k-2} from the bounds of Program 2 (tree_enum.py).  For every admissible prime s the two
remaining primes p < q satisfy, with A' = A s, B' = B (s-1), C' = a B' - b A' > 0,

        (C' p - a B') (C' q - a B') = N := b (a A' B' + eps C'),

and both factors are positive.  So t = C' p - a B' is a divisor of N with t = -a B' (mod C') and t <= sqrt(N).
Instead of enumerating p over its interval, or factoring N, we find all divisors of N in that residue class
below sqrt(N) by an exact lattice-point count on the hyperbola  (r + c u)(r' + c v) = N  (divisors_in_class).
Every step is integer arithmetic; nothing is factored except in the rare case that the modulus is too small
for the lattice method to be quick; then N is factored by FLINT and every prime factor is proved prime
(proved_prime: 13 strong bases below 3.3e24, FLINT's primality prover above).
"""
import sys, math
import numpy as np
import gmpy2, flint
from gmpy2 import mpz, isqrt, invert, gcd, is_prime

sys.setrecursionlimit(20000)

# ---------------------------------------------------------------------------------------------------------
# exact bounds, as in tree_enum.py (Program 2)

def exact_upper(T_num, T_den, m):
    """largest p with (p/(p-1))^m > T_num/T_den."""
    T = T_num / T_den
    g = int(1 / (1 - T ** (-1.0 / m))) + 2
    def cond(p): return p ** m * T_den > (p - 1) ** m * T_num
    while not cond(g): g -= 1
    while cond(g + 1): g += 1
    return g

def exact_upper_ge(T_num, T_den, m):
    """largest p with (p/(p-1))^m >= T_num/T_den > 1."""
    T = T_num / T_den
    g = int(1 / (1 - T ** (-1.0 / m))) + 2
    def cond(p): return p ** m * T_den >= (p - 1) ** m * T_num
    while g > 2 and not cond(g): g -= 1
    while cond(g + 1): g += 1
    return g

def exact_lower(num, den):
    """smallest integer p >= 2 with p/(p-1) < num/den (num > den > 0)."""
    p = num // (num - den) + 1
    while not (p * den < (p - 1) * num): p += 1
    while p - 1 >= 2 and ((p - 1) * den < (p - 2) * num): p -= 1
    return p

def interval(A, B, pj, m, a, b, eps):
    """the interval [lo, hi] for the next prime, exactly as in tree_enum.run."""
    W = (pj + 1) ** m
    if eps == -1:
        hi = exact_upper(a * B, b * A, m)
        lo = exact_lower(a * B * W + b, b * A * W)
    else:
        hi = exact_upper_ge(a * B * W - b, b * A * W, m)
        lo = exact_lower(a * B, b * A)
    return lo, hi

# ---------------------------------------------------------------------------------------------------------
# primes in an interval (segmented sieve)

_small = None
def _small_primes(limit):
    global _small
    if _small is None or _small[-1] < limit:
        L = max(limit, 1 << 16)
        s = np.ones(L + 1, dtype=bool); s[:2] = False
        for i in range(2, int(L ** 0.5) + 1):
            if s[i]: s[i * i::i] = False
        _small = np.nonzero(s)[0]
    return _small

def primes_in(lo, hi):
    """all primes in [lo, hi] as a numpy int64 array (hi < 2^62)."""
    lo = max(lo, 2)
    if hi < lo: return np.zeros(0, dtype=np.int64)
    r = math.isqrt(hi)
    sp = _small_primes(r + 1)
    sp = sp[sp <= r]
    out = []
    SEG = 1 << 22
    a = lo
    while a <= hi:
        b = min(hi, a + SEG - 1)
        seg = np.ones(b - a + 1, dtype=bool)
        for p in sp:
            p = int(p)
            st = max(p * p, ((a + p - 1) // p) * p)
            if st > b: continue
            seg[st - a::p] = False
        idx = np.nonzero(seg)[0] + a
        out.append(idx.astype(np.int64))
        a = b + 1
    return np.concatenate(out) if out else np.zeros(0, dtype=np.int64)

# ---------------------------------------------------------------------------------------------------------
# divisors of N in a residue class

def _first(A, M, L, R):
    """least y >= 0 with L <= (A y mod M) <= R, where 0 <= L <= R < M; None if there is none."""
    A %= M
    if L == 0: return 0
    if A == 0: return None
    y = (L + A - 1) // A
    if A * y <= R: return y
    z = _first(M % A, A, (-R) % A, (-L) % A)
    if z is None: return None
    return (L + M * z + A - 1) // A

class Stats:
    def __init__(self): self.boxes = 0; self.hits = 0; self.direct = 0; self.factored = 0; self.found = 0

def divisors_in_class(N, c, r, tmax, stats=None, kappa=1.0, max_boxes=None):
    """All t with t | N, t = r (mod c) and 1 <= t <= tmax, in increasing order; None if the lattice method
    would need more than max_boxes boxes (the caller then factors N).

    A common factor g of r and c must divide t, so it is split off first.  Divisors above sqrt(N) are the
    cofactors N/t' of divisors t' <= sqrt(N) in the class N/r (mod c), so only t <= sqrt(N) is ever searched
    for, by _small_divisors_in_class."""
    N = mpz(N); c = mpz(c); r = mpz(r) % c; tmax = mpz(tmax)
    scale = mpz(1)
    while True:
        g = gcd(r, c)
        if g == 1: break
        if N % g: return []
        N //= g; r //= g; c //= g; tmax //= g; scale *= g
    if c == 1:
        return None
    s = isqrt(N)
    out = _small_divisors_in_class(N, c, r, min(tmax, s), stats, kappa, max_boxes)
    if out is None: return None
    if tmax > s:
        rp = (N * invert(r, c)) % c
        co = divisors_in_class(N, c, rp, s, stats, kappa, max_boxes)
        if co is None: return None
        out = out + [N // x for x in co if s < N // x <= tmax and (N // x) % c == r]
    return sorted(scale * t for t in out)

def _small_divisors_in_class(N, c, r, tmax, stats, kappa, max_boxes):
    """divisors_in_class for gcd(r, c) = 1, c >= 2 and tmax <= sqrt(N).

    Write t = r + c u and N/t = r' + c v with r' = N r^{-1} mod c.  Then c u v + r' u + r v = w0 := (N - r r')/c,
    so v = alpha - beta u (mod c) with alpha = w0/r, beta = r'/r mod c.  The u-range [0, U] is cut into boxes
    [u0, u1]; in a box, v lies in [v_lo, v_hi] where v_lo, v_hi come from N/(r + c u1) and N/(r + c u0).  If the
    box is shorter than c in the v direction, the admissible u are exactly those with
    (alpha - beta u) mod c in the residues of [v_lo, v_hi]; they are listed by _first in O(log c) steps each,
    and each is then tested by one exact division.  Otherwise the u of the box are tested one by one."""
    if tmax < r: return []
    U = (tmax - r) // c
    ri = invert(r, c)
    rp = (N * ri) % c
    w0 = (N - r * rp) // c
    alpha = (ri * w0) % c
    a0 = (-(ri * rp)) % c
    # boxes [u0, u0 + w) with w = ratio * u0 hold about kappa lattice points when v ~ N/(c^2 u)
    lg = 3 * math.log(c) - math.log(N) + math.log(kappa)
    g_box = math.exp(min(lg, 600.0))
    ratio = (g_box + math.sqrt(g_box * g_box + 4 * g_box)) / 2
    wcap = max(2, int(kappa * float(c)))
    if max_boxes is not None:
        if ratio < 1:
            est = (1 + math.log(max(2.0, float(U) * ratio))) / ratio
        else:
            est = math.log(float(U) + 2) / math.log1p(ratio) + 2
        if est > max_boxes: return None
    out = []
    u = mpz(0)
    nb = 0
    while u <= U:
        fw = float(u) * ratio
        if fw < 2:
            t = r + c * u
            if N % t == 0: out.append(t)
            if stats: stats.direct += 1
            u += 1
            continue
        w = wcap if fw >= wcap else int(fw)
        u1 = min(U, u + w - 1)
        nb += 1
        t0 = r + c * u; t1 = r + c * u1
        vhi = (N // t0 - rp) // c                     # v <= floor((floor(N/t0) - r')/c)
        q1 = -((-N) // t1)                             # ceil(N/t1)
        vlo = -((rp - q1) // c)                        # v >= ceil((ceil(N/t1) - r')/c)
        H = vhi - vlo + 1
        if H <= 0:
            u = u1 + 1; continue
        if H >= c:
            x = u
            while x <= u1:
                t = r + c * x
                if N % t == 0: out.append(t)
                x += 1
            if stats: stats.direct += int(u1 - u + 1)
            u = u1 + 1; continue
        nx = u1 - u + 1
        b1 = (alpha + a0 * u - vlo) % c
        x = mpz(0); bc = b1
        while True:
            if bc < H:
                y = 0
            else:
                L = c - bc
                y = _first(a0, c, L, L + H - 1)
                if y is None: break
            x += y
            if x >= nx: break
            t = r + c * (u + x)
            if stats: stats.hits += 1
            if N % t == 0: out.append(t)
            x += 1
            bc = (b1 + a0 * x) % c
        u = u1 + 1
    if stats: stats.boxes += nb
    return out

# ---------------------------------------------------------------------------------------------------------
# factoring fallback (FLINT), with proved prime factors

PSI13 = 3317044064679887385961981          # Sorenson-Webster: 13 prime bases suffice below this bound
_BASES13 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)

def proved_prime(n):
    """True iff n is prime, with proof: strong probable-prime tests to the 13 smallest prime bases below
    PSI13 (Sorenson-Webster), FLINT's fmpz_is_prime (Pocklington/Morrison/APR-CL, a proof) above."""
    n = int(n)
    if n < 2: return False
    for p in _BASES13:
        if n % p == 0: return n == p
    if n < PSI13:
        return all(gmpy2.is_strong_prp(n, a) for a in _BASES13)
    return bool(flint.fmpz(n).is_prime())

def factor_proved(N):
    """[(p, e)] with N = prod p^e and every p proved prime.  The factorisation is FLINT's; the primality of
    each factor is proved independently by proved_prime."""
    N = int(N)
    fac = [(int(p), int(e)) for p, e in flint.fmpz(N).factor()]
    prod = 1
    for p, e in fac:
        if not proved_prime(p): raise RuntimeError(f"factor {p} of {N} not proved prime")
        prod *= p ** e
    if prod != N: raise RuntimeError("factorisation does not multiply out")
    return fac

def divisors_by_factoring(N, c, r, tmax):
    divs = [1]
    for p, e in factor_proved(N):
        divs = [d * p ** i for d in divs for i in range(e + 1) if d * p ** i <= tmax]
    return sorted(mpz(d) for d in divs if d % c == r % c)

# ---------------------------------------------------------------------------------------------------------
# the search

def admissible(p, chosen):
    for q in chosen:
        if (p - 1) % q == 0 or (q - 1) % p == 0: return False
    return True

def two_prime_completions(chosen, A, B, a, b, eps, stats=None, max_boxes=50000, cands=None, kappa=1.0):
    """all primes p < q with p > max(chosen) such that n = A p q satisfies b (n + eps) = a phi(n).

    Every divisor t found gives integers p < q with b (A p q + eps) = a B (p-1)(q-1); if cands is a list, those
    in which p or q is composite are appended to it as (p, q, 'p' or 'q'), naming a factor that fails a
    strong probable-prime test (so is certainly composite)."""
    A = mpz(A); B = mpz(B)
    C = a * B - b * A
    if C <= 0: return []
    N = b * (a * A * B + eps * C)
    tmax = isqrt(N)
    r = (-a * B) % C
    # below about 10^45 factoring is cheaper than a long run of boxes
    mb = min(max_boxes, int(3 * 2 ** (len(str(N)) / 4)))
    ts = divisors_in_class(N, C, r, tmax, stats=stats, kappa=kappa, max_boxes=mb)
    if ts is None:
        ts = divisors_by_factoring(N, C, r, tmax)
        if stats: stats.factored += 1
    sols = []
    pmax = max(chosen) if chosen else 1
    for t in ts:
        p, rem = divmod(t + a * B, C)
        assert rem == 0
        q, rem = divmod(N // t + a * B, C)
        if rem: continue                  # possible only when gcd(aB, C) > 1
        if p <= pmax or q <= p: continue
        assert b * (A * p * q + eps) == a * B * (p - 1) * (q - 1)
        if stats: stats.found += 1
        if not gmpy2.is_prime(p):
            if cands is not None: cands.append((int(p), int(q), 'p'))
            continue
        if not gmpy2.is_prime(q):
            if cands is not None: cands.append((int(p), int(q), 'q'))
            continue
        if proved_prime(p) and proved_prime(q):
            sols.append((int(A * p * q), tuple(chosen) + (int(p), int(q))))
    return sols

def frontier(k, pmin, a, b, eps, stop_m):
    """the nodes at depth k - stop_m of the search tree of tree_enum.run, as (chosen, A, B, lo, hi) with the
    exact interval [lo, hi] for the next prime (empty intervals are dropped)."""
    out = []
    stack = [((), 1, 1)]
    while stack:
        chosen, A, B = stack.pop()
        j = len(chosen); m = k - j
        if b * A >= a * B: continue
        pj = chosen[-1] if chosen else 1
        lo, hi = interval(A, B, pj, m, a, b, eps)
        lo = max(lo, pj + 1, pmin)
        if hi < lo: continue
        if m == stop_m:
            out.append((chosen, A, B, lo, hi)); continue
        children = [int(p) for p in primes_in(lo, hi) if admissible(int(p), chosen)]
        for p in reversed(children):
            stack.append((chosen + (p,), A * p, B * (p - 1)))
    return out

def admissible_mask(ss, chosen):
    """numpy mask of the s in ss with q not dividing s - 1 for every q in chosen (s > max(chosen))."""
    mask = np.ones(len(ss), dtype=bool)
    for q in chosen:
        mask &= (ss % q) != 1
    return mask

def three_prime_node(chosen, A, B, lo, hi, a, b, eps, stats=None, max_boxes=50000, cands=None):
    """all solutions n = A s p q with s in [lo, hi] (s prime, admissible) and p, q from two_prime_completions.
    Returns (number of s treated, solutions)."""
    ss = primes_in(lo, hi)
    ss = ss[admissible_mask(ss, chosen)]
    sols = []
    for s in ss.tolist():
        sols += two_prime_completions(chosen + (s,), A * s, B * (s - 1), a, b, eps, stats=stats,
                                      max_boxes=max_boxes, cands=cands)
    return len(ss), sols
