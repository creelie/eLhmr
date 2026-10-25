# Targeted construction pass, 25 October 2026

This register records the particular routes examined. It does not claim to
exhaust every possible mathematical proof or every future construction.

## Lehmer

1. **Uniform construction for every factor count: proved.** The new appendix
   gives finite quotient and prime bounds, a forced final prime, and proofs
   of termination and completeness for every prescribed k. This is not an
   all-k emptiness proof. The general existence of fixed-count algorithms
   is already in the literature and is not claimed as a new breakthrough.
2. **Direct exact implementation: verified within stated ranges.** The
   explicit-stack implementation has no fixed recursion-depth cutoff on k.
   It reproduces all six known composite companion solutions through k=6,
   completes the minus-sign cases k=2 through 13, and passes independent
   small-prime comparisons. The budgeted k=14 traversal is incomplete.
3. **A scale-uniform contraction of sum(1/D): fails for the untruncated
   prefix graph.** Fix an independent odd-prime prefix with A,B,M and
   D=MB-A>0, gcd(A,MB)=1. Primes p=2 modulo A, p odd and sufficiently
   large, preserve the prefix gcd condition and have D'=Dp-MB>0.
   The reciprocal-prime sum in this invertible progression diverges, and
   1/D'>1/(Dp). Thus the sum of 1/D' over these prime children diverges.
   Each fixed-k tree still has a finite prime cutoff; the obstruction is
   to a contraction uniform over all unrestricted remaining lengths.
   It does not disprove other weighted potentials or future arithmetic prunes.
4. **Fixed congruence filters: insufficient by themselves.** The earlier
   fixed-modulus lemma constructs arbitrarily long prime lists passing the
   specified modular and gcd filters. They fail the necessary tail-size test,
   so they are not examples satisfying all Lehmer constraints. The combined
   exact-divisibility, ordering and primality exclusion remains unproved.
5. **Prime-preserving factorization descent: missing an existence step.**
   The last-two-factor identity turns the problem into a divisor pair with
   congruence constraints. Moving to a different compatible pair would only
   be a descent after proving the recovered entries are primes above the
   fixed prefix. No theorem ensuring that pair was found. A swap merely
   interchanges the two existing factors and does not give a smaller solution.
6. **Geometric resolution or one-variable Vieta substitution: no closure.**
   The last-three-entry equation is linear in each variable separately,
   so fixing two entries supplies no second root for that variable. A
   resolution of its rational surface does not by itself classify the
   prime integral points. No prime-integral-point exclusion was obtained.

The new title is "A certified sixteen-prime-factor lower bound for Lehmer's
totient problem." The numeral sixteen describes the proved manuscript
bound; it is not replaced by an unsupported full-resolution title.

## Polya-Vinogradov

1. **Follow the exact formal input: dependency confirmed.** The unchanged
   original and added closed Mobius endpoints invoke the credited OpenAI
   nonvanishing theorem. Rechecking those sources does not change authorship
   or give an independent argument. Successful historical source builds and
   the matching proof tree are identified separately from fresh checks.
2. **Use the Mobius converse as a replacement: circular in the current
   proof.** The supplied estimate was obtained from nonvanishing. Applying
   the converse to it returns a consequence of that input, rather than an
   independent proof of the input.
3. **Weaker independent target: conditional implication proved.** A suitable
   DH mean-square estimate at H=D^(21/20) would give exponent 15/16+epsilon
   by sixth-power extraction. The arithmetic parameter calculation is exact.
   The required estimate for the actual Mobius coefficients is not proved.
4. **An arbitrary-coefficient large-sieve shortcut: false.** Sixth-power
   rows all equal 1 on prime columns for order-six characters. Their
   contribution contradicts the overly strong coefficient-independent DH
   estimate in the needed range. The proof and finite-field identity checks
   are in the supplement. They do not refute the specialized Mobius estimate.
5. **Restrict to squarefree rows and apply a quadratic sieve: loses the
   rows needed for extraction.** The useful sixth-power rows are removed.
   No independent estimate is recovered by this restriction.
6. **Classical periodicity and Euler product: do not reach the target.**
   Character periodicity controls sums of chi(n), not of mu(n)chi(n). Absolute Euler
   products give nonvanishing only to the right of 1. A reciprocal contour
   shift into a left half-plane requires the very nonvanishing under study.
7. **Replace the citation with another recent exposition: dependency
   retained.** The original README still identifies the source as a preprint.
   The provisional reading notes consulted explicitly retain a transfer
   estimate from the original argument. Neither is relabeled as a refereed
   theorem or an independent proof in this revision.

## Release scope

These are accurately scoped research revisions, consistent with the user's
earlier instruction to archive current research. A new DOI archives these
results, programs and limitations. It does not certify full Lehmer closure,
an independent fixed zero-free region, peer review, acceptance or a prize.
The added written material requires author review before new submission
declarations are selected. No journal or Hexagon submission is performed.
