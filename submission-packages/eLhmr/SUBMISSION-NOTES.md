# Lehmer's totient problem with fewer than sixteen prime factors — submission package

Files in this folder:

- `lehmer-totient-journal.pdf` — the manuscript, 44 pages, 18 figures (amsart, 11pt, one column). It is
  `paper/journal.tex` of https://github.com/creelie/eLhmr at release v1.4.0, the journal version:
  the results, proofs, searches and checks of the archive paper, with the fifty-six solutions of
  the test equation as Appendix A and a closing section that states and proves the assertion
  equivalent to Lehmer's conjecture, with two constraints on its divisor D.
- `lehmer-totient-journal-tex.zip` — the LaTeX source with the 18 figures as PNG;
  `pdflatex journal.tex` three times compiles it on its own (TeX Live with amsart, lmodern,
  microtype, booktabs, enumitem, hyperref). This is the single tex.zip for the journal and for
  Hexagon.
- `AI-PROVENANCE.md` — the provenance statement, for the Hexagon AI field and for any journal
  form that asks for it.
- `COVER-LETTER-IJNT.md` — the cover letter to the International Journal of Number Theory.
- `SHA256SUMS` — checksums of the files.

The same PDF and zip are in the repository as `paper/paper1/` and `paper/paper2/`, and in the
release v1.4.0, https://github.com/creelie/eLhmr/releases/tag/v1.4.0, which the paper cites. The version DOI will be added when Zenodo
assigns it.

## What the paper claims

Theorem 1.1: a composite n with phi(n) | n-1 has at least sixteen distinct prime factors, at least
16001 if (n-1)/phi(n) >= 3, and more than 10^8 if 3 | n. Theorem 1.2: n < 2^(2^(k-7)) for k prime
factors. Theorems 1.3 to 1.6: the nine known solutions of phi(n) | n+1 are the only ones with at
most eight prime factors, a further one prime to 3 has at least sixteen, and the Fermat-type
solutions are the closure of 1 under one- and two-prime extensions. Theorem 1.7 (Meijer, Yamada)
is reproved by the large sieve. Lehmer's conjecture is not claimed; Proposition 9.1 states the
equivalent assertion, and the paragraph after it records that its divisor D equals (A-1)/(q-1),
is odd and is congruent to -A modulo 2^|S|.

Every reference was checked against its registration record (Crossref or Zenodo) on 21 October
2026.

## Journal: International Journal of Number Theory (World Scientific)

Chosen because it charges nothing on the subscription route (an article-processing charge is
invoiced only if Gold Open Access is chosen after acceptance) and because the publisher's AI rule
is disclosure of the tool and of its use, with the decision left to the editor; the paper's
declaration does this. Submit the PDF through the journal's online system; the LaTeX source is
asked for after acceptance. Fallback: The Ramanujan Journal (Springer, hybrid, no charge unless
open access is chosen). Integers and Experimental Mathematics are excluded by their rules on
AI-drafted text. The journals' pages could not be opened from the session that prepared this;
confirm the current instructions on the journal page before submitting.

Earlier decisions to mention if the form asks: rejected by the Journal of Number Theory (as a
partial result) and desk-rejected by Mathematics of Computation; the manuscript is not under
consideration elsewhere.

Form fields:

- Title: Lehmer's totient problem with fewer than sixteen prime factors
- Author: Deep Bhattacharjee — ORCID 0000-0003-0466-750X — itsdeep@live.com — Formerly,
  Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
- MSC 2020: primary 11A25; secondary 11A41, 11A51, 11D68, 11N36, 11Y11, 11Y16, 11Y70.
- Keywords: Lehmer's totient problem; Euler's totient function; large sieve; Fermat primes.
- Abstract: as on the first page of the PDF (the plain-text version is in the Hexagon section).
- Funding: none. Competing interests: none. Data: https://github.com/creelie/eLhmr/releases/tag/v1.4.0.

## Hexagon (hexagonmath.org) — v1 deposit

- Files: `lehmer-totient-journal.pdf` and `lehmer-totient-journal-tex.zip` (no code; Hexagon
  does not accept code, and the programs are linked from the Data and code availability section).
- Title: Lehmer's totient problem with fewer than sixteen prime factors
- Contributor: Deep Bhattacharjee — ORCID 0000-0003-0466-750X — itsdeep@live.com — Formerly,
  Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
- Subject: math.NT (number theory).
- MSC 2020: primary 11A25; secondary 11A41, 11A51, 11D68, 11N36, 11Y11, 11Y16, 11Y70.
- Keywords: Lehmer's totient problem; Euler's totient function; large sieve; Fermat primes;
  Carmichael numbers.
- Abstract (plain text): A composite number n whose totient divides n-1 was known to have at
  least fourteen prime factors. We prove that it has at least sixteen, at least 16001 if
  (n-1)/phi(n) >= 3, and more than 10^8 if 3 | n, and that n < 2^(2^(k-7)) if n has k prime
  factors. For the companion equation phi(n) | n+1 we show that the nine known solutions are the
  only ones with at most eight prime factors, and that a further solution prime to 3 has at least
  sixteen. Each statement is reduced by hand to a finite computation, which independent programs
  carry out. Lehmer's conjecture remains open, and we state the assertion that would settle it.
- AI label: a mix of human-written and AI-generated text; human understanding: all parts.
  Statement: the text of `AI-PROVENANCE.md`.
- License: CC BY 4.0.
- Related work: code and data at https://github.com/creelie/eLhmr, release v1.4.0,
  https://github.com/creelie/eLhmr/releases/tag/v1.4.0; earlier releases are archived on Zenodo, concept DOI 10.5281/zenodo.23243779.
