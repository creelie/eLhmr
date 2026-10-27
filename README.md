# A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

## Current research revision: v1.10.0

Author: Deep Bhattacharjee. Prepared 27 October 2026.
The full Lehmer totient conjecture remains unproved.

This revision enlarges three finite-search results of the paper, each by
two programs written independently where the paper says so:

- every composite solution of φ(n) | n−1 exceeds 10^35 (Theorem 1.3; Pinch's
  poster reported 10^30), by the tree search of Section 3 with a size rule
  (Section 5.3, `tree_below.c`, `tree_below.py`, logs in `logs/tree_below/`);
- a quotient (n−1)/φ(n) ≥ 3 forces at least 18001 distinct prime factors
  (was 16001), and 3 | n forces more than 10^9 (was 10^8), by the
  branch-and-bound of Proposition 2.5 at K = 18000 and K = 10^9
  (`bound/independent_list.c`, `bound/independent.c`, logs in `bound/logs/`);
- the size bounds n < 2^(2^(k−17981)) for the quotient ≥ 3 and
  n < 2^(2^(k−10^9)) for 3 | n (Theorem 1.2).

The earlier results of v1.9.0 (sixteen prime factors, the exact final-prime
derivations, the deletion obstruction and the two-prime factorisation) are
retained. No all-factor-count exclusion is claimed.

## Current files

- [Paper_5 package](Paper_5%20package/README.md): the current manuscript,
  complete editable source, submission fields, correspondence and check records.
- [Submission source](paper/main.tex): standard amsart; pdfLaTeX; no margin
  line numbers. The built paper and its source packages are in dist/.
- [Proof scope](Paper_5%20package/VERIFICATION.md): historical and fresh checks.
- [Final-prime audit](Paper_5%20package/research/FINAL-PRIME-AUDIT.md): targeted
  derivations and a checked obstruction to a proposed uniform descent lemma.

Earlier v1.5.0-v1.8.0 submissions, dist/ builds and their logs are historical
records. They are not competing current submission instructions. The separate
paper/journal.tex target is a legacy shortened version.

## Archive and preprint

Release v1.10.0 follows this revision; its version DOI is recorded here when
Zenodo mints it. Previous release: https://github.com/creelie/eLhmr/releases/tag/v1.9.0 ,
DOI [10.5281/zenodo.23680044](https://doi.org/10.5281/zenodo.23680044); the
concept DOI of all versions is [10.5281/zenodo.23243779](https://doi.org/10.5281/zenodo.23243779).
Prior confirmed archive: https://doi.org/10.5281/zenodo.23638948 .
Original preprint: https://hexagonmath.org/2610.00454v1 . A replacement
identifier has not been assigned. No journal submission or acceptance is claimed.

## Verification and attribution

Fresh computations for this revision are the searches listed above; their
programs and logs are in the repository, and Section 5.3, Section 2.1 and
Appendix D of the paper state which counts were obtained by two programs.
The earlier complete searches and the full Lean project are not rerun. Historical partial Lean checks retain their stated
coverage; they do not prove the full conjecture.

Code remains under its existing MIT licence; the manuscript retains CC BY 4.0.
The earlier archive's human creators retain their bibliography credit. AI
assistance and the pending author review of the added material are disclosed.
