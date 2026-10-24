# Full Lehmer totient conjecture: targeted attempts, 24 October 2026

The target is: for every composite integer n, phi(n) does not divide n-1.
No proof of this target was obtained in this work. The finite sixteen-factor
bound and the new all-length reductions must not be presented as that proof.

## 1. Eliminate the quotient and isolate one integer

Let S be a nonempty set of distinct odd primes. Write A=prod(S),
B=prod(p-1), r=max(S), m=ceil(A/B) and d=mB-A. A prime completion q>r
exists for the Lehmer sign exactly when d divides A-1 and
q=1+(A-1)/d is a prime greater than r.

Complete proof: for any odd q>r with Aq-1=M B(q-1),
M-A/B=(A-1)/(B(q-1)). Telescoping over all integers 3,...,r gives
A/B <= r/2, and q-1 >= r+1. Thus 0<M-A/B<1/2. Since A is odd and B
is even, A/B is not integral and M=ceil(A/B). The converse follows by
substituting d(q-1)=A-1. This is not a novelty claim for the ceiling observation.

What remains: prove the exclusion for **every** S, with no upper bound
on its size or its largest element. Removing M as a search variable does not
remove this quantifier. The M=2 computation in the original paper was already
working with a fixed quotient, so this simplification does not by itself
advance its k=16 frontier.

## 2. Residues of the final defect

If the candidate is a prime above S, then
3<=d<B/2, d is odd, A=1 (mod d), mB=1 (mod d), and gcd(d,mAB)=1.
Every prime ell dividing d is absent from S and none of the prefix primes
is 1 modulo ell. If ell=3, all prefix primes are 2 modulo 3, their number
is even, and m=1 modulo 3. In particular m=2 excludes ell=3.

Proof: d divides A-1 and mB=A+d. These give both congruences and
coprimality. The parity of A and B gives odd d; d=1 gives q=A and
cannot give a prime above S. The ceiling proof gives d<B/2. For ell=3,
the two excluded residues force each p=2, so B=1 and A=(-1)^|S| modulo 3.

What remains: none of these conditions contradicts arbitrary prefix length.
The upstream full paper already studies prime factors of the defect, including
the stronger finite exclusions for a sixteen-factor candidate. Those results
are credited to that paper, not claimed as newly obtained here.

## 3. A prime-preserving descent through the last two entries

Fix A,B,M and put C=MB-A>0. For the equation
A*p*q-1=MB*(p-1)*(q-1), the exact transformation is

    (C*p-MB)*(C*q-MB)=M*A*B-C = N.

Set t=C*p-MB and u=C*q-MB, with 0<t<u. Then tu=N and both factors
are congruent to -MB modulo C. Conversely any such complementary pair,
after checking integrality, order and primality of p=(t+MB)/C and
q=(u+MB)/C, gives a solution of the same equation.

For 0<t<t'<=sqrt(N), the expression t+N/t strictly decreases. Hence

    p*q = (N+(MB)^2+MB*(t+N/t))/C^2

strictly decreases when t is replaced by a larger compatible divisor t'.
This is a valid arithmetic descent **if** such a t' gives two primes still
above the fixed prefix. No theorem guaranteeing that t' exists was found.
Replacing the factors by arbitrary integers loses the primality condition.
A minimal hypothetical counterexample is therefore not contradicted merely
by this transformation.

## 4. Three-entry geometry and blowups

For fixed prefix products A,B the equation with three entries is
F(x,y,z)=Axyz-1-MB(x-1)(y-1)(z-1)=0. It has degree one in each
variable. Fixing two entries determines the third uniquely; it supplies
no second root for a one-variable Vieta descent.

For M=2, the upstream full paper proves that F is not a product of three
affine linear forms plus a constant (Proposition 9.7). Blowing up a
rational surface or resolving a geometric singularity would require an
additional proof about its integral points and the primality of the recovered
entries. No such prime-preserving construction or resulting contradiction
was obtained. Naming the transformation would not supply that missing proof.

## 5. Why a primality-free bypass fails

The eLhmr full paper supplies a 25-entry tuple of odd integers prime to 3
satisfying prod(x)+1=2 prod(x-1), and constructs minus-sign tuples from it
for every length at least 26. These are not tuples of distinct primes.
Thus an argument using only the relaxed product equation, parity, avoidance
of 3 and the stated gcd conditions cannot exclude all lengths. The supplied
tuple is checked independently in verification/relaxed-equation-barrier.json.

## Present outcome

Fresh exhaustive k=15 execution completed all 55,443 tasks and all
33,865,004 admissible p13 values, with zero integer candidate completions.
The new ceiling reduction has a written proof valid for all prefix lengths,
and finite independent consistency tests. These are concrete results, but
the all-prefix exclusion remains open. No full-closure, Annals acceptance,
or award claim is supported.
