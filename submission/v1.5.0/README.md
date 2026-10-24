# Lehmer totient research release v1.5.0

**The full Lehmer totient conjecture remains open.** This release retains the
sixteen-prime-factor theorem and the other bounds stated in the manuscript.
It adds the written ceiling reduction and one-candidate criterion for every
prime prefix (Proposition 9.2 and Corollaries 9.3–9.4), and portable primality
certificates for all 41 distinct stored k=14 factors. The elementary reductions
are not claimed as novel general exclusions.

Author: Deep Bhattacharjee, preserving the current public Hexagon/eLhmr byline.
The earlier Mandal–Bhattacharjee–Bhattacharya archive is cited with all creators.

Manuscript DOI: https://doi.org/10.5281/zenodo.23617604
Release: https://github.com/creelie/eLhmr/releases/tag/v1.5.0
Original preprint: https://hexagonmath.org/2610.00454v1
Original source commit: fd398ef410faeca431c3c5bab142f3443e857cdf

The replacement Hexagon identifier remains pending. No Hexagon v2 or aiXiv
identifier is invented. This is a research archive and a submission preparation
packet; it is not a journal acceptance or a proof of the full conjecture.

The master in manuscript/main.tex uses aomart screen mode without margin line
numbers. The journal, Hexagon and aiXiv copies use the same mathematical PDF.
Build from manuscript/ with pdflatex twice. All 21 original TikZ diagrams were
regenerated as vector PDFs; the manuscript uses 18 of them.

VERIFICATION.md separates fresh computations, stored-data checks, prior CI
and searches not rerun. Full exhaustive searches are not Lean-formalised.
FULL-CONJECTURE-ATTEMPTS.md and VALUATION-ROUTE.md record the precise remaining
gaps, including the absence of an all-length stopping bound.

Portable checks (Python standard library; run without -O):

    python lucas_certificates.py --verify verification/k14-lucas-certificates.json
    python single_candidate.py
    python valuation_route.py

The manuscript and newly written prose are CC BY 4.0. Original code retains
its MIT license (ORIGINAL-CODE-LICENSE); new Python verification code is MIT.
No private conversation logs are included. AI-PROCESS-NOTES.md describes the
publicly shareable research process and the manuscript identifies AI use.

The Annals cover letter is an unsent draft. Editorial assessment, novelty and
suitability remain matters for independent reviewers. The packet contains no
claim of guaranteed acceptance, priority for an unproved conjecture or prize.
