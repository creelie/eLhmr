# A precise test of a fixed-residue approach to Lehmer's problem

25 October 2026. Research note; no novelty or full-conjecture claim.

## What this attempt proves

Fix a positive integer L and a positive integer k. There exist k distinct
odd primes with product A and B = product(p-1) such that

* gcd(A,B)=1;
* A-1 = 2B modulo L;
* for D=2B-A, gcd(D,L)=gcd(D-1,A)=1 and ceil(A/B)=2;
* A/B < 4/3, so A-1 is not 2B.

The primes can all exceed any prescribed bound. Thus a fixed finite list of
congruence moduli, even with the two displayed exact gcd filters, cannot by
itself distinguish all these prime tuples from a quotient-two solution.
This is a limitation of this particular proposed sieve, not an impossibility
theorem about computational or congruence-based proofs of Lehmer's conjecture.

## Proof

Inductively construct p_j. Let A_0=B_0=1, and let A_{j-1},B_{j-1} be
the previous products. Require

    p_j = 1 (mod 2L),       p_j = 2 (mod A_{j-1}).

All earlier primes exceed 2L, so gcd(2L,A_{j-1})=1. The Chinese remainder
theorem gives one invertible residue class modulo 2L A_{j-1}. The classical
Dirichlet theorem on primes in arithmetic progressions gives a prime in
that class exceeding all previous primes, 2 B_{j-1}+1, 2^(j+2)+1 and
the prescribed bound. This uses an established classical theorem, not an
unrefereed research preprint.

For i<j, p_j-1=1 modulo p_i, while p_j>p_i-1. Hence no p_i divides any
p_j-1 and gcd(A,B)=1. Also A=1 and B=0 modulo L, proving the congruence
and D=-1 modulo L.

At the stage p_i is adjoined, B_i=-B_{i-1} modulo p_i. Later factors
p_j-1 are 1 modulo p_i. Consequently

    D-1 = 2B-A-1 = -2 B_{i-1}-1 (mod p_i).

The strictly positive number 2 B_{i-1}+1 is less than p_i by construction,
so p_i does not divide D-1. This proves gcd(D-1,A)=1.

Finally, using log(1+x)<x for x>0,

    0 < log(A/B) < sum_{j=1}^k 2^(-j-2) < 1/4.

The elementary series inequality exp(1/4)<1/(1-1/4)=4/3 proves the stated
ratio. In particular 1<A/B<2, ceil(A/B)=2 and A-1<2B. This completes the
lemma for every k, with no finite computational cutoff.

## Why this is not a Lehmer closure

These tuples FAIL an already known necessary size test for a prime
completion. Indeed D>2B/3>B/2, whereas a prime tail above the prefix in
the one-candidate reduction requires D<B/2. They are controls for the
listed modular and gcd filters, not examples satisfying all constraints.
Nothing here proves that the simultaneous divisibility, ordering and
primality conditions are impossible for every other prefix.

For every nonempty finite set S of distinct odd primes, put

    A=product(S), B=product(p-1), m=ceil(A/B), D=mB-A.

The remaining all-prefix obligation is to prove that at least one of

    D divides A-1;
    q=1+(A-1)/D is prime;
    q>max(S)

fails. No such universal exclusion or global bound on |S| is established
by this note. The current sixteen-factor manuscript remains a partial
result on the full totient conjecture.

## Exact controls

lehmer_fixed_modulus.py constructs examples for L=1,2,6,30. Every example
prime is checked by trial division, all equations use integers or exact
fractions, and the failed size test is explicitly asserted. The universal
lemma rests on the proof above, not on these four examples.

Classical reference for the existence step: H. Davenport, Multiplicative
Number Theory, third edition, Springer, 2000, Dirichlet's theorem on primes
in arithmetic progressions. No claim of an independent proof of that
classical theorem is made.
