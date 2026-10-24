# Independent primality certificates for the fifteen long k=14 nodes

The stored factorizations contain 41 distinct factors, some with 41 decimal
digits. The original check script calls SymPy's `isprime`; beyond its stated
deterministic range, that alone is a probable-prime test. This revision also
verifies each factor using FLINT's rigorous routine and supplies independent
Lucas certificates whose verification uses Python's standard library only.

## Criterion and full proof

Let n>2 and suppose the complete factorization

    n-1 = product(q^e)

is known, with each distinct q already proved prime. If an integer a satisfies

    a^(n-1) = 1 modulo n,
    gcd(a^((n-1)/q)-1,n) = 1 for every q dividing n-1,

then n is prime.

Proof. Let r be any prime divisor of n. The first condition shows r does
not divide a and the order t of a in the group (Z/rZ)^* divides n-1.
The gcd conditions show that t does not divide (n-1)/q for any q dividing n-1.
Because t divides n-1, this forces v_q(t)=v_q(n-1) for every such q.
Therefore t=n-1. Lagrange's theorem gives n-1<=r-1, hence r>=n.
Since r divides n and n>=2, this implies r=n, so n is prime.

## Finite verification

Every q in each factorization is recursively certified by the same criterion,
terminating at the base prime 2. The verifier checks exact multiplication of
all q^e, strict decrease of recursive prime arguments, modular powers, gcds,
all root certificates and absence of unused certificate nodes. It does not
import FLINT, SymPy or a probable-prime test. FLINT only discovers the
factorizations during generation.

    python lucas_certificates.py --verify verification/k14-lucas-certificates.json

This certifies the stored factors. The fresh no-factorization k=7..15 searches
are a separate verification route. Neither check proves the full Lehmer
totient conjecture, which still requires exclusion at every prime-factor count.
