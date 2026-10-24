# Targeted valuation attempt and the exact remaining gap

24 October 2026. This note records a proof attempt, not a full closure.

For a nonempty finite set S of distinct odd primes put A=prod(S),
B=prod(p-1), M=ceil(A/B), N=MB and D=N-A. Suppose D divides A-1,
and put Q=1+(A-1)/D. Then the two exact identities are

    D(Q-1)=A-1,       AQ-1=N(Q-1).

The proposed new route was to exploit the multiplicities of shared prime
factors of the numbers p-1: their valuations add in B, whereas a Carmichael
condition alone only accounts for a maximum. The test below determines
whether that supplies an additional restriction after the exact reduction.

## All-length valuation calculation

Assume gcd(D,N)=1, as is necessary for a prime completion. For every prime
ell dividing N the first identity gives

    v_ell(A-1)=v_ell(Q-1),

and the second gives

    v_ell(AQ-1)=v_ell(N)+v_ell(A-1).

Thus the full multiplicity budget is already enforced by D dividing A-1.
It is not an additional contradiction. This conclusion concerns this
specific attempted filter; it does not rule out every possible valuation argument.

Let U be the largest divisor of A-1 all of whose prime factors divide N,
and put V=(A-1)/U. Then gcd(V,N)=1 and

    D divides A-1  if and only if  D divides V.

Proof: gcd(D,N)=1 implies gcd(D,U)=1, so Euclid's lemma proves the
equivalence. U and V can be computed by repeatedly dividing A-1 by its gcd
with N, without factoring A-1. This is an exact computational simplification,
but its all-length equivalence shows that it adds no new mathematical exclusion.

There is also a useful prefix gcd identity. When gcd(D,A)=1,

    gcd(Q,A)=gcd(D-1,A),

because DQ=A+D-1 and multiplication by D is invertible modulo A.
A prime Q>max(S) therefore requires gcd(D-1,A)=1. This is a necessary
prefix filter, not a sufficient primality criterion and not a novelty claim.

## A concrete control

The supplied spoof examples in the eLhmr full manuscript include

    (3,5,17,257,65717,23794275).

The first five entries are primes. They give M=2, D=181 and the last
entry Q=23794275, which is composite and shares factors with the prefix.
The exact product identity and valuation conditions hold. Thus those
identities alone do not force the divisibility test to fail, or force Q to be
prime. The additional gcd filter rejects this example; it is not a
counterexample to the full collection of necessary conditions for a Lehmer number.
The example is from the supplied manuscript, not newly discovered here.

## What would constitute full closure

For every finite set S of smaller odd primes, one must prove that D fails
to divide A-1, or that Q is not a prime greater than max(S). A computational
proof could do this using a proved global stopping bound or an independently
verified finite certificate whose induction covers all lengths. No such bound,
certificate or all-prefix contradiction was obtained by this valuation attempt.

The words "for every finite set" are the remaining mathematical obligation.
The fact that each fixed length has a terminating search does not prove
termination of all searches at once. The current release remains an audited
sixteen-prime-factor result with explicit reductions, not a proof of the full conjecture.

## Further local-residue attempt

The new gcd requirement is not a contradiction by itself. For defect 5 and
quotient 2, the local conditions A=2B=1 modulo 5 allow the residue list
(2,2,4), followed by any number of blocks (2,2,2,2). A block has product 1
modulo 5 and its shifted product is 1. This proves compatibility of those
local conditions at arbitrarily many lengths. It does not construct primes
with exact defect 5, nor does it establish the exact divisibility condition.

The genuine prime prefix (7,17,19) has A=2261, B=1728, M=2 and D=1195.
It passes gcd(A,B)=gcd(D-1,A)=1 and A=2B=1 modulo 5, but D does not divide
A-1. It is a control for the individual tests, not a counterexample to their
conjunction or to Lehmer's conjecture. The conjunction still lacks an
all-prefix exclusion proof. See residue_route.py for exact checks.
