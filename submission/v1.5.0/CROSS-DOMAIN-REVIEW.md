# Primary-literature and Anaxia review, 24 October 2026

No complete proof of the integer Lehmer totient conjecture was obtained from
these sources. This is a targeted review of the listed works, not a claim to
have checked every paper in the literature.

## Published constructions and their exact scope

**Molnar and Singh, Spoof Lehmer Factorizations, Integers 26 (2026), A33.**
Published 20 February 2026; DOI 10.5281/zenodo.18714466.
https://math.colgate.edu/~integers/aa33/aa33.pdf
Preprint: https://arxiv.org/abs/2409.17076v2

They give a finite algorithm for each fixed number of positive bases, and
list the cases with at most six bases. Composite bases permit spoof solutions.
This is useful for exact enumeration and countertests of proposed algebraic
arguments. It does not supply a uniform upper bound on the number of prime
factors. Running a terminating algorithm separately for each length does not
prove that the entire infinite sequence of searches terminates.

**Ji and Qin, Lehmer's totient problem over F_q[x], C. R. Math. 355 (2017),
370-377.** DOI 10.1016/j.crma.2017.03.007.
https://www.numdam.org/item/10.1016/j.crma.2017.03.007.pdf

Their main theorem classifies the polynomial analogue: for q>=4 no reducible
solution exists, with explicitly classified exceptions for q=2,3. The proof
uses cyclotomic factorisation and primitive divisors for powers of a common
finite-field cardinality. This is a genuine complete result in a different
setting. Integer prime factors do not come as powers of one common cardinality.
A map preserving both the relevant cardinalities and divisibility would be
required to transfer the theorem; none was constructed here. For example,
F3 x F3 has 9 elements and 4 units, so its unit count divides 9-1, whereas
Z/9Z has 6 units. Passing to arbitrary products of fields does not preserve
the integer totient problem.

**Tarnauceanu, Generalizing Lehmer's totient problem, Elemente der Mathematik.**
DOI 10.4171/EM/492.
https://ems.press/content/serial-article-files/44957

Theorem 1.1 classifies finite groups G with |Aut(G)| dividing |G|-1 as cyclic
groups of prime or Lehmer order. The proof forces cyclicity but explicitly
retains the unknown Lehmer-order case. Applying it to a cyclic group of
order n returns the original condition; it does not exclude composite n.

**Yamada, On Lehmer's problem and related problems, arXiv:2303.16853v3.**
https://arxiv.org/abs/2303.16853v3

Theorem 2 gives M < 16.03235 log log omega(N) in its stated range. These are
strong explicit sieve estimates. For fixed M=2 the bound is compatible with
arbitrarily large omega(N). It cannot by itself turn the search into one finite
computation. The original manuscript already credits the underlying sieve work.

## Proposed closures must be checked independently

**Norman, A group-theoretical approach to Lehmer's totient problem,
arXiv:2106.11781v1.** https://arxiv.org/pdf/2106.11781

Its Lemma 2.1 asserts a lower bound that fails for C2 x C2 x C5: the sum of
element orders is 147, so psi(G)/|G|^2=147/400 < 2/5=phi(5)/(2*5).
This counterexample is already identified in the user's manuscript; it was
independently recomputed by enumerating the 20 group elements here. It is not
a new discovery attributed to this revision. In this construction the
Klein-four factor has sum of element orders 7, not a normalized sum >=1/2.
The claimed exclusion of M=2 cannot be imported from that lemma.

**Zriaa, arXiv:2302.07368.** https://arxiv.org/abs/2302.07368

The current arXiv record is withdrawn and explicitly reports an error in
Theorem 2.3. Its abstract's claimed closure cannot serve as a proved input.

**Zhuang, Some Bounds on the Lehmer Index, arXiv:2610.18943v1**, submitted
13 October 2026. https://arxiv.org/abs/2610.18943v1

This recent preprint studies estimates in terms of reciprocal sums and another
restriction when 3 divides n. It does not claim full closure. It was screened
for relevant constructions; no reliance on it was added to the revised proof.

## What was actually inspected in BLLM/Anaxia

Local source commit: a85ae17fdf77796cdedd17d98558f4269b3771d5.
https://github.com/creelie/eBLLM

- `construct/lehmer_equiv.py` implements the final-divisor reformulation,
  small finite searches and companion positive controls. Its own module text
  explicitly says it settles nothing new about the full conjecture.
- Its five deterministic unit tests were freshly run and passed. No model
  subagents or proposer calls were run.
- `bllm/agents.py` implements its symbolic `BlowUpAgent` as substitution
  x -> x^k in polynomial identities for k=2,3,4. For a prime x and k>1 this
  is composite, so this operation is not a prime-preserving descent for Lehmer.
- `bllm/certificates.py` implements exact rational/Sturm checks for
  spherical-code auxiliary polynomials inspired by the certificate method of
  Cohn-Elkies and Viazovska. These certificates concern Gegenbauer coefficients
  and inner products; no Lehmer exclusion certificate is supplied by that code.
- Its `lehmer-totient` control explicitly marks the full problem open and
  records the all-prefix obstruction. The separate sixteen-factor control is
  a partial result. Those statuses were not changed.

## A precise transfer-matrix reduction

For a prefix define A=prod p, B=prod(p-1), D=MB-A. Appending a factor x gives

    A' = x A,   D' = (x-1)D-A.

Thus the vector (A,D) is multiplied by T_x=[[x,0],[-1,x-1]]. All these
matrices commute, and the fixed change of coordinates (A,D)->(A,A+D)
simultaneously diagonalizes them to diag(x,x-1). This is proved simply by
A'+D'=(x-1)(A+D). Starting from (1,M-1), a Lehmer solution would end at
(n,-1), with all generators distinct primes and their product n.

Consequently a spectral argument using only simultaneous diagonalization
recovers the original two products. It supplies no extra inequality or prime
restriction. A possible research route is a well-founded invariant for these
**prime-generated** orbits which excludes D=-1. No such invariant was found.
An invariant for arbitrary odd generators cannot work: the supplied relaxed
26-entry tuple reaches the minus-sign equation and includes composite entries.
The cross-gcd constraints in that example do not assert pairwise coprimality
of the entries themselves; it does not refute a proposed argument that also
uses pairwise coprimality. Such an argument would need a separate proof.

## The exact unresolved step

For every nonempty finite set S of distinct odd primes, define A,B as above,
m=ceil(A/B), d=mB-A. Full closure requires proving that d does not divide A-1,
or that 1+(A-1)/d is not a prime greater than max(S), for **every** S.
Neither a new all-length exclusion nor a global bound on |S| was proved.
These notes are a record of tested routes and missing implications, not a
full-conjecture manuscript.
