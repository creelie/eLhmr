# Lehmer's totient problem with fewer than sixteen prime factors — journal package

Files in this folder:

- `lehmer-totient-journal.pdf` — the manuscript, 44 pages, 18 figures (amsart, 11pt). This is `paper/journal.tex` of
  https://github.com/creelie/eLhmr: the results, proofs, searches and checks of the archive paper without its Section 9
  and appendices, which stay in the archive, and with a closing section that states and proves the assertion equivalent
  to Lehmer's conjecture.
- `lehmer-totient-journal-tex.zip` — the LaTeX source with the 18 figures as PNG; `pdflatex journal.tex` three times
  compiles it on its own (TeX Live with amsart, lmodern, microtype, booktabs, enumitem, hyperref).
- `SHA256SUMS` — checksums of the two files.

## What the paper claims

Theorem 1.1: a composite n with phi(n) | n-1 has at least sixteen distinct prime factors, at least 16001 if
(n-1)/phi(n) >= 3, and more than 10^8 if 3 | n. Theorem 1.2: n < 2^(2^(k-7)) for k prime factors. Theorems 1.3 to 1.6:
the nine known solutions of phi(n) | n+1 are the only ones with at most eight prime factors, a further one prime to 3
has at least sixteen, and the Fermat-type solutions are the closure of 1 under one- and two-prime extensions.
Theorem 1.7 (Meijer, Yamada) is reproved by the large sieve. Lehmer's conjecture is not claimed; Proposition 9.1
states the equivalent assertion.

## Where to send it

Integers (math.colgate.edu/~integers) is excluded: its instructions say the narrative and all wording must be the
authors' and not AI-generated, and the paper's declaration says Claude drafted text. Taylor & Francis (Experimental
Mathematics) forbids generative AI first drafts of a manuscript or its sections. Both would require withdrawing the
declaration, which the paper will not do.

Recommended, in order (neither charges anything on the subscription route; the publishers' pages could not be
opened from the session that prepared this, so confirm on the journal page before submitting):

1. **International Journal of Number Theory** (World Scientific). No page charge; an article-processing charge is
   invoiced only if Gold Open Access is chosen after acceptance. The publisher's AI rule is disclosure of the tool and
   of how it was used, with the final decision left to the editor; the paper's declaration already does this. Submit
   the PDF through the journal's online system; the LaTeX source is asked for after acceptance.
2. **The Ramanujan Journal** (Springer). Hybrid: no charge unless open access is chosen. Springer's policy allows
   large language models with documentation in the manuscript; AI cannot be an author.
3. **Journal de Théorie des Nombres de Bordeaux** (free, subscription route) as a further option.

## Cover letter

Dear Editor,

I submit the manuscript "Lehmer's totient problem with fewer than sixteen prime factors" for consideration.

Lehmer asked in 1932 whether a composite n can satisfy phi(n) | n-1. The best refereed bound was Cohen and Hagis's
fourteen prime factors (1980); fifteen was announced by Renze and by Pinch without a refereed proof. The paper proves
that a composite solution has at least sixteen distinct prime factors, at least 16001 when (n-1)/phi(n) >= 3 and more
than 10^8 when 3 | n, and that a solution with k prime factors is below 2^(2^(k-7)), which divides the number of
binary digits allowed by the bound of Burek and Zmija by 128. For the companion equation phi(n) | n+1 it proves that
the nine known solutions are the only ones with at most eight prime factors and that a further solution prime to 3
has at least sixteen, the first refereed bounds for that equation. The new ingredient is a treatment of the last
three prime factors together, as a divisor of an explicit integer in a residue class found by lattice reduction or by
a short scan of a fixed sum, which reduces the case of fifteen primes to a quarter of an hour of computation.

Each statement is reduced by hand to a finite computation, and every computation was carried out by at least two
independently written programs, one of which never factors an integer, so that its negative answers depend on no
primality proof; the programs were also run on equations with known solutions. The programs, their recorded output
and Lean 4 proofs of the statements that do not depend on a search are archived on Zenodo (doi:10.5281/zenodo.23243779).
The paper does not claim Lehmer's conjecture; its closing proposition states the assertion equivalent to it.

The manuscript is 44 pages with 18 figures. It has not been published and is not under consideration elsewhere. The
use of an AI tool in writing the programs and the Lean proofs and in drafting text is declared at the end of the
manuscript; I reviewed and edited all of it and take full responsibility for the content. MSC 2020: primary 11A25;
secondary 11A41, 11A51, 11D68, 11N36, 11Y11, 11Y16, 11Y70. Keywords: Lehmer's totient problem, Euler's totient
function, large sieve, Fermat primes.

Yours sincerely,

Deep Bhattacharjee (itsdeep@live.com, ORCID 0000-0003-0466-750X)

## Hexagon (hexagonmath.org) deposit — what to enter

- Files: the same `lehmer-totient-journal.pdf` and `lehmer-totient-journal-tex.zip` (no code; the programs are linked
  from the Data and code availability section).
- Title: Lehmer's totient problem with fewer than sixteen prime factors
- Contributor: Deep Bhattacharjee — ORCID 0000-0003-0466-750X — itsdeep@live.com — Formerly, Electro-Gravitational
  Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
- Subject: math.NT (number theory).
- Keywords: Lehmer's totient problem; Euler's totient function; large sieve; Fermat primes; Carmichael numbers.
- Abstract (plain text): A composite number n whose totient divides n-1 was known to have at least fourteen prime
  factors. We prove that it has at least sixteen, at least 16001 if (n-1)/phi(n) >= 3, and more than 10^8 if 3 | n,
  and that n < 2^(2^(k-7)) if n has k prime factors. For the companion equation phi(n) | n+1 we show that the nine
  known solutions are the only ones with at most eight prime factors, and that a further solution prime to 3 has at
  least sixteen. Each statement is reduced by hand to a finite computation, which independent programs carry out.
  Lehmer's conjecture remains open, and we state the assertion that would settle it.
- AI label: a mix of human-written and AI-generated text; human understanding: all parts. Statement: Claude
  (Anthropic) was used to write and run the programs, to write the Lean proofs and to draft text; the contributor
  reviewed and edited all of it, every statement is proved in the text or reduced to a recorded computation, and the
  contributor takes full responsibility for the content.
- License: CC BY 4.0.
- Related work: code and data at https://github.com/creelie/eLhmr, archived at https://doi.org/10.5281/zenodo.23243779
  (concept DOI; v1.2.0 is 10.5281/zenodo.23282630).
