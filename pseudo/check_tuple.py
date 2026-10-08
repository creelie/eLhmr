#!/usr/bin/env python3
"""Independent check of a pseudo-solution, written separately from the search (plain Python integers only).
usage: check_tuple.py FILE EPS     FILE: one decimal integer per line"""
import sys, math
sys.set_int_max_str_digits(0)

def check(xs, eps):
    k = len(xs)
    assert all(x >= 5 for x in xs), "entry below 5"
    assert all(x % 2 == 1 for x in xs), "even entry"
    assert all(x % 3 != 0 for x in xs), "entry divisible by 3"
    assert all(xs[i] < xs[i + 1] for i in range(k - 1)), "not increasing"
    P = 1; Q = 1
    for x in xs:
        P *= x; Q *= x - 1
    assert P + eps == 2 * Q, "equation fails"
    for i, x in enumerate(xs):
        for j, y in enumerate(xs):
            assert math.gcd(x, y - 1) == 1, f"gcd(x_{i+1}, x_{j+1} - 1) > 1"
    return P, Q

if __name__ == "__main__":
    xs = [int(l) for l in open(sys.argv[1]) if l.strip()]
    eps = int(sys.argv[2])
    P, Q = check(xs, eps)
    print(f"OK: k = {len(xs)}, eps = {eps:+d}, all {len(xs)**2} gcd conditions hold, entries odd, prime to 3, increasing")
    print("digits of entries:", [len(str(x)) for x in xs])
    print("digits of the product:", len(str(P)))
