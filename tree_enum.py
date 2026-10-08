#!/usr/bin/env python3
"""
Program 2: exhaustive search, by enumeration only, for squarefree n = p_1 < ... < p_k (odd primes, p_1 >= pmin) with

        b (n + eps) = a phi(n),        eps = -1: Lehmer's equation n - 1 = M phi(n);  eps = +1: n + 1 = M phi(n).

Iterative depth-first traversal with an explicit stack, integer arithmetic throughout, bounds from a
floating-point guess corrected by exact integer comparisons.  At depth k-2 the prime p_{k-1} is enumerated
over its whole interval and the last prime is read off from  t = C p - a B,  t | b (A p + eps),
q = 1 + b (A p + eps) / t.  Nothing is ever factored.  The root uses p_0 = 1, so that
phi(n) >= B_j (p_j + 1)^(k-j) holds at every depth (the remaining primes are odd, hence p_i - 1 >= 2).
"""
import sys, time, math
from sympy import isprime, primerange

def exact_upper(T_num, T_den, m):
    """largest p with (p/(p-1))^m > T = T_num/T_den, from a float guess corrected exactly."""
    T = T_num / T_den
    g = int(1 / (1 - T ** (-1.0 / m))) + 2
    def cond(p): return p ** m * T_den > (p - 1) ** m * T_num       # (p/(p-1))^m > T  exactly
    while not cond(g): g -= 1
    while cond(g + 1): g += 1
    return g

def exact_upper_ge(T_num, T_den, m):
    """largest p with (p/(p-1))^m >= T = T_num/T_den > 1."""
    T = T_num / T_den
    g = int(1 / (1 - T ** (-1.0 / m))) + 2
    def cond(p): return p ** m * T_den >= (p - 1) ** m * T_num
    while g > 2 and not cond(g): g -= 1
    while cond(g + 1): g += 1
    return g

def exact_lower(num, den):
    """smallest integer p >= 2 with p/(p-1) < num/den (num > den > 0), i.e. (p-1) num > p den... careful:
       p/(p-1) < num/den  <=>  p den < (p-1) num  <=>  p (num - den) > num  <=>  p > num/(num-den)."""
    p = num // (num - den) + 1
    while not (p * den < (p - 1) * num): p += 1
    while p - 1 >= 2 and ((p - 1) * den < (p - 2) * num): p -= 1
    return p

def run(k, pmin=5, log=None, a=2, b=1, eps=-1):
    # equation: b (n + eps) = a phi(n);  eps = -1 is Lehmer's first problem, eps = +1 the second
    nodes = 0; leaves = 0; sols = []; maxrange = 0
    stack = [((), 1, 1)]           # (chosen, A = prod p, B = prod (p-1))
    while stack:
        chosen, A, B = stack.pop()
        nodes += 1
        j = len(chosen); m = k - j
        if b * A >= a * B: continue                              # P = A/B >= a/b
        pj = chosen[-1] if chosen else 1
        W = (pj + 1) ** m
        if eps == -1:
            hi = exact_upper(a * B, b * A, m)                    # (p/(p-1))^m > T = aB/(bA)
            lo = exact_lower(a * B * W + b, b * A * W)           # p/(p-1) < T + 1/(A W)  [rest = T + 1/(P phi)]
        else:
            hi = exact_upper_ge(a * B * W - b, b * A * W, m)     # (p/(p-1))^m >= T - 1/(A W)  [rest = T - 1/(P phi)]
            lo = exact_lower(a * B, b * A)                       # p/(p-1) < T
        lo = max(lo, pj + 1, pmin)
        if hi < lo: continue
        if m == 2:
            leaves += 1
            maxrange = max(maxrange, hi - lo)
            C = a * B - b * A
            if C <= 0: continue
            for p in primerange(lo, hi + 1):
                bad = False
                for q in chosen:
                    if (p - 1) % q == 0 or (q - 1) % p == 0: bad = True; break
                if bad: continue
                t = C * p - a * B
                if t <= 0: continue
                num = b * (A * p + eps)
                if num % t: continue
                q = 1 + num // t
                if q <= p or not isprime(q): continue
                ok = True
                for r in chosen + (p,):
                    if (q - 1) % r == 0 or (r - 1) % q == 0: ok = False; break
                if not ok: continue
                n = A * p * q; phi = B * (p - 1) * (q - 1)
                if b * (n + eps) == a * phi:
                    sols.append((n, chosen + (p, q)))
                    if log: print("SOLUTION", n, chosen + (p, q), file=log, flush=True)
            continue
        children = []
        for p in primerange(lo, hi + 1):
            bad = False
            for q in chosen:
                if (p - 1) % q == 0 or (q - 1) % p == 0: bad = True; break
            if not bad: children.append(p)
        for p in reversed(children):
            stack.append((chosen + (p,), A * p, B * (p - 1)))
    return nodes, leaves, maxrange, sols

if __name__ == "__main__":
    for k in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        t0 = time.time()
        nodes, leaves, mr, sols = run(k)
        print(f"k={k:2d} nodes={nodes:8d} leaves={leaves:8d} maxrange={mr} time={time.time()-t0:7.1f}s sols={sols}", flush=True)
