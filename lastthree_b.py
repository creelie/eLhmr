#!/usr/bin/env python3
"""
Second, independent implementation of the three-prime completion (compare lastthree.py).

Differences from lastthree.py, on purpose:
  * the nodes at depth k - 3 come from the rational bounds of Program 1 (tree_search.Search.bounds);
  * the primes s are produced by gmpy2.next_prime (which can return a pseudoprime but never skips a prime,
    so at worst an extra composite s is treated), and admissibility is tested by a plain loop;
  * the hyperbola  c u v + r' u + r v = w0  (t = r + c u, N/t = r' + c v) is cut into boxes along v,
    not along u, and the lattice points of each box are enumerated from a Lagrange-reduced basis of the
    lattice {(u, v) : r' u + r v = 0 (mod c)} in the metric that makes the box a square;
  * a lattice point is accepted when it satisfies the equation above exactly (not by a trial division);
  * when factoring is used, primality of every factor is proved by FLINT's fmpz_is_prime.
"""
import sys, os, math
from fractions import Fraction as Fr
import gmpy2, flint
from gmpy2 import mpz, isqrt, invert, gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tree_search import Search

class StatsB:
    def __init__(self): self.boxes = 0; self.points = 0; self.factored = 0; self.found = 0

def frontier_rational(k, pmin, a, b, eps, stop_m):
    """nodes at depth k - stop_m with the interval for the next prime, from Program 1's rational bounds."""
    S = Search(k, a, b, pmin=pmin, eps=eps); out = []
    def primes(lo, hi):
        p = gmpy2.next_prime(lo - 1)
        while p <= hi:
            yield int(p); p = gmpy2.next_prime(p)
    def dfs(chosen, P, A, B):
        m = k - len(chosen)
        if P >= S.mu: return
        T = S.mu / P; pj = chosen[-1] if chosen else 1
        hi, lo = S.bounds(T, P, B, pj, m); lo = max(lo, pj + 1, pmin)
        if hi < lo: return
        if m == stop_m:
            out.append((tuple(chosen), A, B, lo, hi)); return
        for p in primes(lo, hi):
            if S.ok_prime(p, chosen): dfs(chosen + [p], P * Fr(p, p - 1), A * p, B * (p - 1))
    dfs([], Fr(1), 1, 1)
    return out

def _lagrange(b1, b2, wu, wv):
    """Lagrange-reduce the basis b1, b2 of a planar lattice for the form Q(x, y) = (x wv)^2 + (y wu)^2."""
    def Q(x): return (x[0] * wv) ** 2 + (x[1] * wu) ** 2
    def Bf(x, y): return x[0] * y[0] * wv * wv + x[1] * y[1] * wu * wu
    if Q(b2) < Q(b1): b1, b2 = b2, b1
    while True:
        q1 = Q(b1)
        mu = (2 * Bf(b1, b2) + q1) // (2 * q1)          # nearest integer to <b1,b2>/<b1,b1>
        b2 = (b2[0] - mu * b1[0], b2[1] - mu * b1[1])
        if Q(b2) >= q1: return b1, b2
        b1, b2 = b2, b1

def _points_in_box(P0, e1, e2, ua, ub, va, vb):
    """all points P0 + i e1 + j e2 with ua <= u <= ub and va <= v <= vb."""
    D = e1[0] * e2[1] - e1[1] * e2[0]
    corners = [(ua, va), (ua, vb), (ub, va), (ub, vb)]
    inum = [(x - P0[0]) * e2[1] - (y - P0[1]) * e2[0] for x, y in corners]   # i = inum / D
    jnum = [e1[0] * (y - P0[1]) - e1[1] * (x - P0[0]) for x, y in corners]   # j = jnum / D
    if D < 0:
        D = -D; inum = [-x for x in inum]; jnum = [-x for x in jnum]
    i0 = -((-min(inum)) // D); i1 = max(inum) // D
    j0 = -((-min(jnum)) // D); j1 = max(jnum) // D
    out = []
    if i1 < i0 or j1 < j0: return out
    for i in range(int(i0), int(i1) + 1):
        for j in range(int(j0), int(j1) + 1):
            u = P0[0] + i * e1[0] + j * e2[0]; v = P0[1] + i * e1[1] + j * e2[1]
            if ua <= u <= ub and va <= v <= vb: out.append((u, v))
    return out

def divisors_b(N, c, r, stats=None, kappa=2.0, max_boxes=5000):
    """all t <= sqrt(N) with t | N and t = r (mod c), gcd(r, c) = 1, c >= 2; None if too many boxes."""
    N = mpz(N); c = mpz(c); r = mpz(r) % c
    assert c >= 2 and gcd(r, c) == 1
    sN = isqrt(N)
    sc = sN if sN * sN == N else sN + 1                  # t <= sqrt(N)  <=>  N/t >= sc
    if r > sN: return []
    rp = (N * invert(r, c)) % c
    w0 = (N - r * rp) // c
    U = (sN - r) // c                                     # u <= U
    out = []
    if N % r == 0: out.append(r)                          # u = 0
    if U < 1: return out
    # v runs over [vmin, vtop]: N/t >= sc and t >= r + c
    vmin = -((rp - sc) // c)
    vtop = (N // (r + c) - rp) // c
    if vtop < vmin: return out
    beta = (invert(r, c) * rp) % c                         # lattice: v = -beta u (mod c)
    alpha = (invert(r, c) * w0) % c                        # coset: v = alpha - beta u (mod c)
    g = kappa * float(c) ** 3 / float(N)
    lr = math.log1p(max(g, math.sqrt(g)))                 # box [v, rho v] holds about kappa points
    if lr * max_boxes < math.log(float(vtop) / max(1.0, float(vmin)) + 1.0): return None
    rho = math.exp(lr)
    va = vmin; nb = 0
    while va <= vtop:
        vb = min(vtop, max(va, int(float(va) * rho)))
        # u range for v in [va, vb]:  t = N/(r' + c v)
        ua = -((r - (-((-N) // (rp + c * vb)))) // c)     # ceil((ceil(N/(r'+c vb)) - r)/c)
        ub = (N // (rp + c * va) - r) // c
        ua = max(ua, 1); ub = min(ub, U)
        nb += 1
        if ua <= ub:
            wu = ub - ua + 1; wv = vb - va + 1
            e1, e2 = _lagrange((mpz(1), (-beta) % c), (mpz(0), c), wu, wv)
            v0 = va + ((alpha - beta * ua - va) % c)
            for u, v in _points_in_box((ua, v0), e1, e2, ua, ub, va, vb):
                if stats: stats.points += 1
                if c * u * v + rp * u + r * v == w0:
                    out.append(r + c * u)
        va = vb + 1
    if stats: stats.boxes += nb
    return sorted(set(out))

def divisors_by_factoring_b(N, c, r):
    N = int(N); sN = int(isqrt(N))
    fac = flint.fmpz(N).factor()
    prod = 1
    for p, e in fac:
        if not flint.fmpz(p).is_prime(): raise RuntimeError(f"unproved factor {p}")
        prod *= int(p) ** int(e)
    assert prod == N
    divs = [1]
    for p, e in fac:
        p = int(p); e = int(e)
        divs = [d * p ** i for d in divs for i in range(e + 1) if d * p ** i <= sN]
    return sorted(mpz(d) for d in divs if d % c == r % c)

def completions_b(chosen, A, B, a, b, eps, stats=None, cands=None, max_boxes=5000):
    A = mpz(A); B = mpz(B)
    C = a * B - b * A
    if C <= 0: return []
    N = b * (a * A * B + eps * C)
    r = (-a * B) % C
    g = gcd(r, C)
    if g > 1 or C == 1:
        ts = divisors_by_factoring_b(N, C, r); stats and setattr(stats, 'factored', stats.factored + 1)
    else:
        mb = min(max_boxes, int(2 ** (len(str(N)) / 4)))   # small N: factoring is cheaper
        ts = divisors_b(N, C, r, stats=stats, max_boxes=mb)
        if ts is None:
            ts = divisors_by_factoring_b(N, C, r); stats and setattr(stats, 'factored', stats.factored + 1)
    sols = []; pmax = max(chosen) if chosen else 1
    for t in ts:
        if (t + a * B) % C or (N // t + a * B) % C: continue
        p = (t + a * B) // C; q = (N // t + a * B) // C
        if p <= pmax or q <= p: continue
        if stats: stats.found += 1
        pp = flint.fmpz(int(p)).is_prime(); qp = flint.fmpz(int(q)).is_prime()
        if pp and qp:
            sols.append((int(A * p * q), tuple(chosen) + (int(p), int(q))))
        elif cands is not None:
            cands.append((int(p), int(q), 'q' if pp else 'p'))
    return sols

def node_b(chosen, A, B, lo, hi, a, b, eps, stats=None, cands=None, max_boxes=5000):
    ns = 0; sols = []
    s = gmpy2.next_prime(lo - 1)
    while s <= hi:
        s_ = int(s); s = gmpy2.next_prime(s)
        if any((s_ - 1) % q == 0 for q in chosen): continue
        ns += 1
        sols += completions_b(chosen + (s_,), A * s_, B * (s_ - 1), a, b, eps, stats=stats, cands=cands,
                              max_boxes=max_boxes)
    return ns, sols
