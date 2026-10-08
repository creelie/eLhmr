#!/usr/bin/env python3
"""
Program 1: exact branch-and-bound for squarefree odd n = p_1 < ... < p_k (primes) with

        b (n + eps) = a phi(n),       phi(n) = prod (p_i - 1),     mu = a/b,
        eps = -1: Lehmer's equation (n - 1 = M phi(n));  eps = +1: the companion equation (n + 1 = M phi(n)).

Recursive traversal with rational arithmetic (fractions module).  With P_j = prod_{i<=j} p_i/(p_i-1),
T = mu/P_j, m = k - j primes still to choose, delta = 1/(A_j W), W = (p_j + 1)^m, p_0 = 1:
  (B1)  P_j < mu for every j < k.
  (B2)  eps = -1:  (p/(p-1))^m > T  and  p/(p-1) < T + delta      for p = p_{j+1};
        eps = +1:  (p/(p-1))^m >= T - delta  and  p/(p-1) < T.
  (C)   p_i does not divide p_l - 1 for any i, l;  p_i does not divide a unless it divides b.
  (L)   the last two primes satisfy (C p - aB)(C q - aB) = b (aAB + eps C) with C = aB - bA,
        A = prod_{i<=k-2} p_i, B = prod_{i<=k-2} (p_i - 1).  At a terminal node p is enumerated over its
        interval, or, when the interval is long, the divisors of the right-hand side are enumerated.
"""
import sys, math, time
from fractions import Fraction as Fr
from sympy import isprime, primerange, factorint, divisors

sys.setrecursionlimit(10000)

def iroot_ceil_bound(T, m):
    """largest integer p with p/(p-1) > T^(1/m), i.e. the upper bound for p_{j+1}.  Exact:
       p/(p-1) > T^(1/m)  <=>  (p/(p-1))^m > T.  Binary search on p."""
    # p/(p-1) decreasing in p; find max p with (p/(p-1))^m > T
    lo, hi = 2, 2
    while Fr(hi, hi-1)**m > T: hi *= 2
    # invariant: condition true at lo... ensure lo satisfies
    while hi - lo > 1:
        mid = (lo + hi)//2
        if Fr(mid, mid-1)**m > T: lo = mid
        else: hi = mid
    return lo

def lower_bound(rest):
    """smallest integer p with p/(p-1) < rest, i.e. p > rest/(rest-1)."""
    if rest <= 1: return None
    return math.floor(rest/(rest-1)) + 1

class Search:
    def __init__(self, k, a, b, verbose=False, enum_limit=3_000_000, factor_digits=30, pmin=3, eps=-1):
        self.eps = eps
        self.factor_digits = factor_digits
        self.pmin = pmin
        self.k, self.a, self.b, self.mu = k, a, b, Fr(a, b)
        self.sols = []; self.nodes = 0; self.leaves = 0; self.hard_leaves = 0
        self.max_range = 0; self.verbose = verbose; self.enum_limit = enum_limit
        self.t0 = time.time()

    def bounds(self, T, P, B, pj, m):
        delta = Fr(1, (P * B * (pj + 1)**m))
        if self.eps == -1:
            return iroot_ceil_bound(T, m), lower_bound(T + delta)
        # eps = +1: (p/(p-1))^m >= T - delta ; p/(p-1) < T
        Tm = T - delta
        assert Tm > 1
        lo_, hi_ = 2, 2
        while Fr(hi_, hi_-1)**m >= Tm: hi_ *= 2
        while hi_ - lo_ > 1:
            mid = (lo_ + hi_)//2
            if Fr(mid, mid-1)**m >= Tm: lo_ = mid
            else: hi_ = mid
        return lo_, lower_bound(T)

    def ok_prime(self, p, chosen):
        # (C)
        if self.a % p == 0 and self.b % p != 0: return False
        for q in chosen:
            if (p - 1) % q == 0 or (q - 1) % p == 0: return False
        return True

    def run(self):
        self.dfs([], Fr(1), 1, 1)
        return self.sols

    def dfs(self, chosen, P, A, B):
        self.nodes += 1
        j = len(chosen); m = self.k - j
        if P >= self.mu and j < self.k: return                       # (B1)
        if m == 2:
            self.leaf(chosen, P, A, B); return
        T = self.mu / P
        pj = chosen[-1] if chosen else 1
        hi, lo = self.bounds(T, P, B, pj, m)
        lo = max(lo, pj + 1, self.pmin)
        if hi < lo: return
        for p in primerange(lo, hi + 1):
            if not self.ok_prime(p, chosen): continue
            self.dfs(chosen + [p], P * Fr(p, p - 1), A * p, B * (p - 1))

    def leaf(self, chosen, P, A, B):
        self.leaves += 1
        a, b = self.a, self.b
        C = a * B - b * A
        if C <= 0: return
        D = b * (a * B * A + self.eps * C)
        T = self.mu / P
        pj = chosen[-1] if chosen else 1
        hi, lo = self.bounds(T, P, B, pj, 2)
        lo = max(lo, pj + 1)
        if hi < lo: return
        aB = a * B
        rng = hi - lo
        self.max_range = max(self.max_range, rng)
        self.max_D = max(getattr(self, "max_D", 0), len(str(D)))
        if rng <= self.enum_limit and (len(str(D)) > self.factor_digits or rng < 2000):
            for p in primerange(lo, hi + 1):
                if not self.ok_prime(p, chosen): continue
                d1 = C * p - aB
                if d1 <= 0 or D % d1: continue
                d2 = D // d1
                if (d2 + aB) % C: continue
                q = (d2 + aB) // C
                if q <= p or not isprime(q) or not self.ok_prime(q, chosen + [p]): continue
                self.record(chosen + [p, q])
        else:
            # divisor enumeration
            if len(str(D)) > self.factor_digits:
                self.hard_leaves += 1
                if self.verbose:
                    print(f"  hard leaf: chosen={chosen} range={rng} D~10^{len(str(D))}", flush=True)
            for d1 in divisors(D):
                if (d1 + aB) % C: continue
                p = (d1 + aB) // C
                if p < lo or p > hi or not isprime(p) or not self.ok_prime(p, chosen): continue
                d2 = D // d1
                if (d2 + aB) % C: continue
                q = (d2 + aB) // C
                if q <= p or not isprime(q) or not self.ok_prime(q, chosen + [p]): continue
                self.record(chosen + [p, q])

    def record(self, primes):
        n = 1; phi = 1
        for p in primes: n *= p; phi *= (p - 1)
        assert self.b * (n + self.eps) == self.a * phi, primes
        self.sols.append((n, primes))
        if self.verbose: print(f"  SOLUTION n={n} primes={primes}", flush=True)

def lehmer(k, verbose=False, enum_limit=3_000_000):
    """all composite n with omega(n)=k and phi(n) | n-1.  M ranges over 2 <= M < prod p/(p-1) <= (3/2)(5/4)...:
       bound M by the product over the k smallest odd primes."""
    P = Fr(1); cnt = 0
    for p in primerange(3, 10**6):
        P *= Fr(p, p - 1); cnt += 1
        if cnt == k: break
    Mmax = math.floor(P) if P.denominator != 1 else int(P) - 1
    stats = []
    sols = []
    for M in range(2, Mmax + 1):
        S = Search(k, M, 1, verbose, enum_limit)
        S.run()
        stats.append((M, S.nodes, S.leaves, S.hard_leaves, S.max_range, round(time.time() - S.t0, 1)))
        sols += S.sols
    return sols, stats

if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    sols, stats = lehmer(k, verbose=True)
    for s in stats: print("M=%d nodes=%d leaves=%d hard=%d maxrange=%d time=%ss" % s)
    print("solutions:", sols)
