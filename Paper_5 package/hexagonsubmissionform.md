# Hexagon submission fields

Submit a replacement version of 2610.00454v1; do not create a duplicate work.
The new version identifier is assigned by Hexagon after submission and is not
asserted in advance. Existing record: https://hexagonmath.org/2610.00454v1

## Title

Lehmer's totient problem with fewer than sixteen prime factors

## Abstract - copy the complete block

For a composite number $n$ whose totient divides $n-1$, earlier published work required fourteen prime factors, and computational announcements required fifteen. We prove a lower bound of sixteen, at least $16001$ if $(n-1)/\varphi(n)\ge3$, and more than $10^8$ if $3\mid n$, and that $n<2^{2^{k-7}}$ if $n$ has $k$ prime factors. For the companion equation $\varphi(n)\mid n+1$ we show that the nine known solutions are the only ones with at most eight prime factors, and that a further solution prime to $3$ has at least sixteen. Each statement is reduced by hand to a finite computation, which independent programs carry out. We also give a reduction with one candidate for the largest prime for each prefix. Lehmer's full conjecture remains open.

The block uses explicit TeX commands rather than macros defined only in main.tex.

## Subjects, tags and MSC2020

Primary subject: math.NT
Cross-list subjects: None
Tags: Lehmer totient problem, Euler totient function, prime factors, exhaustive search, primality certificates
MSC2020 primary code: 11A25
MSC2020 additional codes: 11A41, 11A51, 11D68, 11N36, 11Y11, 11Y16, 11Y70
arXiv identifier: leave blank. No arXiv identifier is asserted.

## Contributors - preserve this order

Contributor 1: Deep Bhattacharjee
Affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
ORCID: 0000-0003-0466-750X

The affiliations are former affiliations, not assertions of current employment.

## Authorship and understanding selections

Text: A mix of human-written and AI-generated.
Human understanding: All parts of this contribution have been checked and understood by a human.
The user explicitly supplied both declarations for all six papers on 25 October 2026.

## Provenance statement - copy this paragraph

Claude through Claude Code assisted the original search programs, computational development, partial Lean work and drafting. OpenAI Codex assisted the ceiling and one-candidate reductions, targeted valuation and residue investigations, independent primality certificates, checking the stated finite reproductions, figures, editing and packaging. These efforts do not provide a full-conjecture proof. The submitting author declares that all parts have been
checked and understood by a human and takes responsibility for the content.
The repository contains partial Lean results for statements not depending on the exhaustive search. The full searches and the full Lehmer conjecture are not claimed to be Lean-formalised.

## Tools used

- Anthropic Claude / Claude Code
- OpenAI Codex
- Python
- PARI/GP
- Lean 4 (partial results)
- LaTeX / pdfLaTeX

Use the corresponding system/tool entry if available and Other for an unlisted
tool. Do not invent a model version for an entry that is not documented.

## Formalisation links

https://github.com/creelie/eLhmr/tree/v1.5.0/lean

Scope: The repository contains partial Lean results for statements not depending on the exhaustive search. The full searches and the full Lehmer conjecture are not claimed to be Lean-formalised.
If the portal rejects a host/path, leave it for manual review rather than
uploading Lean material in the article source ZIP.

## Files and licence

Required source ZIP: Lehmers_totient_problem_with_fewer_than_sixteen_prime_factorstex.zip
Reference PDF: Lehmers_totient_problem_with_fewer_than_sixteen_prime_factors.pdf
AI provenance upload: AI_PROVENANCE.md (outside the source ZIP).
Licence selection: CC BY 4.0, matching the existing Hexagon manuscript record.
The manuscript source ZIP contains the article, bibliography and required
figures only. It excludes Lean developments, executables, journal correspondence,
other manuscripts and private model traces. Standard TeX Live classes/packages
are build dependencies rather than relicensed files in this ZIP.

## Review before submitting

Use pdfLaTeX, main document main.tex. The extracted ZIP was rebuilt locally and
its full extracted text and page count matched the supplied PDF. Confirm the
rendered title, abstract, byline, references and final portal preview. This
packet does not press the portal's Process or Submit button on the author's behalf.
