# Hexagon submission fields - prepared revision 1.9.0

## Title

A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

## Abstract

We study composite integers $n$ for which Euler's totient divides $n-1$. The finite-search results give at least sixteen distinct prime factors, at least $16001$ when $(n-1)/\varphi(n)\ge3$, and more than $10^8$ when $3\mid n$. A solution with $k$ prime factors satisfies $n<2^{2^{k-7}}$. For the companion divisibility $\varphi(n)\mid n+1$, the nine known solutions exhaust the cases with at most eight prime factors. We give the written reductions, finite computations and certificate-verification scope separately. For a fixed prime prefix $A=\prod p$, $B=\prod(p-1)$, the quotient is forced to be $M=\lceil A/B\rceil$ and a possible largest prime is uniquely $q=1+(A-1)/(MB-A)$. We derive its exact divisibility, coprimality and valuation consequences, and prove that deleting the largest prime of a hypothetical counterexample cannot yield a smaller Lehmer counterexample. A two-prime factorisation identifies the additional integrality and primality conditions required by a replacement construction. A complete finite construction is proved for every prescribed factor count. Excluding its output at every factor count, or excluding the final prime for every prefix, remains unproved; the full Lehmer conjecture is not resolved.

## Classification

Primary subject: math.NT. Cross-list: none.
MSC2020: Primary 11A25; secondary 11A41, 11A51, 11D68, 11N36, 11Y11, 11Y16, 11Y70.
Tags: Euler totient function, Lehmer totient problem, prime factors, exact completion, exhaustive search.
Original record: https://hexagonmath.org/2610.00454v1 .
Prepare a replacement; its identifier is assigned by Hexagon after submission.
arXiv identifier: leave blank.

## Contributor

Deep Bhattacharjee, ORCID 0000-0003-0466-750X.
Former affiliation: Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
Correspondence: itsdeep@live.com.
The earlier archive's creators remain credited in the manuscript bibliography.

## Text and human understanding

Text: A mix of human-written and AI-generated.
Human understanding: author selection pending for the new appendix and revisions.
The earlier all-parts declaration is retained as historical provenance, not
automatically extended to new material.

## Provenance and tools

Use aiprovinance.md. Tools: Anthropic Claude / Claude Code, OpenAI Codex,
Python, PARI/GP, Lean 4 for specified partial results, LaTeX / pdfLaTeX.
No new complete Lean formalisation or full-conjecture proof is claimed.

## Files and licence

PDF: Lehmer_Sixteen_Prime_Factors_and_Exact_Completions.pdf .
Source ZIP: Lehmer_Sixteen_Prime_Factors_and_Exact_Completionstex.zip; main document main.tex; pdfLaTeX.
AI provenance upload: aiprovinance.md, outside the article source archive.
Manuscript licence: CC BY 4.0, retaining component attribution.
Lean developments are linked separately, not included in the article source ZIP.
Existing checked development: https://github.com/creelie/eLhmr/blob/v1.8.0/lean/UniformFinite.lean .
That link identifies the earlier checked version; the new appendix is not formalised.

No Hexagon submission has been performed. Review the new text before making
the required human-understanding selection.


Confirmed research revision: https://doi.org/10.5281/zenodo.23680044
Release: https://github.com/creelie/eLhmr/releases/tag/v1.9.0
