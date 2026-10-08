#!/usr/bin/env python3
"""The known solutions are found by the lattice route alone.  For every known solution n = A s p q of the
validation equations (the 56 of data/known_solutions.json, with a = 2^k + m, b = 2^k) and of n + 1 = 2 phi(n)
(the Fermat-type solutions with at least three prime factors), both lattice implementations are asked for the
divisors of N in the class of t = C'p - aB' with factoring switched off; t must be among them."""
import sys, json
sys.path.insert(0, ".")
import lastthree as L, lastthree_b as LB
from gmpy2 import mpz, isqrt, gcd
from math import prod

cases = []
known = json.load(open("data/known_solutions.json"))
for k, key in ((4, "S4"), (5, "S5")):
    for n, half in known[key]:
        ps = [2 * h + 1 for h in half]; phi = prod(p - 1 for p in ps)
        assert (2 ** k * (n - 1)) % phi == 0
        cases.append((ps, 2 ** k * (n - 1) // phi, 2 ** k, -1))          # 2^k (n - 1) = (2^k + m) phi(n)
for ps in ([3, 5, 17], [3, 5, 17, 257], [3, 5, 17, 353, 929], [3, 5, 17, 257, 65537],
           [3, 5, 17, 353, 929, 83623937]):
    cases.append((ps, 2, 1, +1))
okA = okB = 0; skipB = 0; oneA = 0
for ps, a, b, eps in cases:
    pre = ps[:-2]; p, q = ps[-2], ps[-1]
    A = mpz(prod(pre)); B = mpz(prod(x - 1 for x in pre))
    C = a * B - b * A; N = b * (a * A * B + eps * C); t = C * p - a * B; r = (-a * B) % C
    assert N % t == 0 and t * t <= N
    if C == 1:
        oneA += 1; continue                      # every integer is in the class: only factoring applies
    ga = L.divisors_in_class(N, C, r, isqrt(N), max_boxes=None)
    if ga is None:
        oneA += 1; continue                      # modulus 1 after removing gcd(r, C)
    okA += t in ga
    if gcd(r, C) == 1:
        gb = LB.divisors_b(N, C, r, max_boxes=10 ** 9)
        okB += t in gb
    else:
        skipB += 1
print(f"{len(cases)} solutions: modulus 1 after reduction (factoring only) for {oneA}; implementation A finds {okA} of "
      f"{len(cases) - oneA}; implementation B finds {okB} of {len(cases) - oneA - skipB} "
      f"(B applies only when gcd(r, c) = 1)")
