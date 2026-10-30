# A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

## Current research revision: v1.11.0

Author: Deep Bhattacharjee (formerly, Electro-Gravitational Space Propulsion
Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of
Calcutta (Heramba Chandra College), 23/49 Gariahat Road, Golpark, Kolkata
700029, West Bengal, India). Correspondence: d.bhattacharjee@erl-forschung.de,
itsdeep@live.com; for GitHub-related contact, egspl@proton.me (GitHub: creelie).
Prepared 30 October 2026. This is the source of version 3 of
https://hexagonmath.org/2610.00454 . The full Lehmer totient conjecture remains
unproved.

This revision:

- raises the bound for a quotient (n−1)/φ(n) ≥ 3, and for (n+1)/φ(n) ≥ 3, to
  at least 20001 distinct prime factors (was 18001), by the branch-and-bound
  of Proposition 2.5 at K = 20000, run by two programs (`bound/independent.py`,
  3,130,127 sets, split into parts with `--part` and `--sub`, part 0 on GitHub
  Actions; `bound/independent_list.c`, 3,131,961 sets; neither finds a set);
  the size bound becomes n < 2^(2^(k−19981));
- proves that every solution of φ(n) | n+1 other than the nine known ones
  exceeds 10^26 (Theorem 1.7), by the size-rule search of Section 5.3 with
  `--eq 2,1,1,3` (`tree_below.c`, 1.4 processor hours; `tree_below.py` agrees
  node for node below 10^21 for 9 ≤ k ≤ 18 and below 10^18 for 2 ≤ k ≤ 16);
  logs `logs/tree_below/companion_*.log`, where the four parts of k = 9 share
  the 5453 nodes above depth 5, 372 of them discarded by size;
- removes the last dependence on unrefereed work: the eight-prime search used
  PARI/GP's BPSW test, whose correctness below 2^64 rests on an unpublished
  table of base-2 pseudoprimes; every prime factor below 2^64 is now certified
  by the strong probable-prime test to the twelve bases 2, …, 37, which is
  proved correct below 3.18·10^23 by Sorenson and Webster (Math. Comp. 2017),
  and the rerun gives the same counts (`companion8/factor_class.gp`);
- corrects the description of the programs and the rounding analysis of
  Proposition 2.5, records the value R_(10^9) of Section 6.5 in
  `bound/logs/ratio_bound_20000.log`, and states that no result depends on
  the preprints of Yamada and Norman;
- shortens the abstract, polishes the text and the appendices, and keeps the
  disclosure of AI assistance to one line of the data availability statement.

The results of v1.10.0 (sixteen prime factors, n > 10^35, more than 10^9
prime factors when 3 | n, the exact final-prime derivations) are retained.
No all-factor-count exclusion is claimed.

## Current files

- [Paper source](paper/main.tex), with its appendices `paper/uniform_all_k.tex`
  and `paper/final_prime_appendix.tex` and the figures in `paper/figures/`:
  amsart, pdfLaTeX. The built paper, its TeX zip and an arXiv tarball are in
  `dist/`.
- The programs and logs named above, with `bound/README.md` for
  Proposition 2.5 and Section 6.5 and `companion8/README.md` for the
  eight-prime search.
- [Paper_5 package](Paper_5%20package/README.md): the v1.9.0 submission
  package, kept as a record; its manuscript is superseded by `paper/`.

Earlier v1.5.0-v1.10.0 submissions, dist/ builds and their logs are historical
records. The separate paper/journal.tex target is a legacy shortened version.

## Archive and preprint

Release v1.11.0: https://github.com/creelie/eLhmr/releases/tag/v1.11.0 ,
version DOI recorded after the release is published.
Previous releases: v1.10.0, DOI
[10.5281/zenodo.23684663](https://doi.org/10.5281/zenodo.23684663), and v1.9.0,
DOI [10.5281/zenodo.23680044](https://doi.org/10.5281/zenodo.23680044); the
concept DOI of all versions is [10.5281/zenodo.23243779](https://doi.org/10.5281/zenodo.23243779).
Preprint: https://hexagonmath.org/2610.00454 (v1 and v2; this release is the
source of v3). No journal submission or acceptance is claimed.

## Verification and attribution

The programs and logs of every search are in the repository, and Sections
2.1, 5.3, 7.5 and 8 and Appendix B of the paper state which counts were
obtained by two programs. The Lean project proves the ten statements listed in
Appendix B; it does not formalise the searches and does not prove the
conjecture.

Code remains under its MIT licence; the manuscript is under CC BY 4.0. The
programs were written and run, and the text was prepared, with the assistance
of AI tools; the author checked the proofs and takes responsibility for the
content.
