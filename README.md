# A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

## Current research revision: v1.9.0

Author: Deep Bhattacharjee. Prepared 27 October 2026.
The full Lehmer totient conjecture remains unproved.

This revision retains the sixteen-prime-factor lower bound and the stated
companion results with their recorded computational scope. It adds exact
final-prime derivations, gcd and valuation consequences, a proof that deletion
of the largest prime cannot preserve a hypothetical Lehmer counterexample,
and a two-prime factorisation with its remaining primality requirement.
No new all-factor-count exclusion is claimed.

## Current files

- [Paper_5 package](Paper_5%20package/README.md): the current manuscript,
  complete editable source, submission fields, correspondence and check records.
- [Submission source](submission/v1.9.0/manuscript/main.tex): standard amsart;
  pdfLaTeX; no margin line numbers. The same current source is in paper/.
- [Proof scope](Paper_5%20package/VERIFICATION.md): historical and fresh checks.
- [Final-prime audit](Paper_5%20package/research/FINAL-PRIME-AUDIT.md): targeted
  derivations and a checked obstruction to a proposed uniform descent lemma.

Earlier v1.5.0-v1.8.0 submissions, dist/ builds and their logs are historical
records. They are not competing current submission instructions. The separate
paper/journal.tex target is a legacy shortened version.

## Archive and preprint

Published release: https://github.com/creelie/eLhmr/releases/tag/v1.9.0 .
Confirmed archival DOI: [10.5281/zenodo.23680044](https://doi.org/10.5281/zenodo.23680044).
The source and master submission ZIPs were created after archive verification.
The DOI identifies the immutable source checkpoint; current receipt additions
do not move that tag. The master ZIP is in submission/v1.9.0 and the release assets.
Prior confirmed archive: https://doi.org/10.5281/zenodo.23638948 .
Original preprint: https://hexagonmath.org/2610.00454v1 . A replacement
identifier has not been assigned. No journal submission or acceptance is claimed.

## Verification and attribution

Fresh checks for this revision cover document compilation, visual review,
exact displayed identities and the supplied pivot-lemma counterexample.
The earlier complete searches and full Lean project are not freshly rerun
locally for this revision. Historical partial Lean checks retain their stated
coverage; they do not prove the full conjecture.

Code remains under its existing MIT licence; the manuscript retains CC BY 4.0.
The earlier archive's human creators retain their bibliography credit. AI
assistance and the pending author review of the added material are disclosed.
