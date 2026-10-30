# Research release v1.11.0

A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

The source of version 3 of https://hexagonmath.org/2610.00454 . The full Lehmer
totient conjecture remains unproved.

- A quotient (n−1)/φ(n) ≥ 3, or (n+1)/φ(n) ≥ 3, forces at least 20001
  distinct prime factors (was 18001): Proposition 2.5(i) at K = 20000, by
  `bound/independent.py` (in four parts) and `bound/independent_list.c`.
  The size bound becomes n < 2^(2^(k−19981)).
- Every solution of φ(n) | n+1 other than the nine known ones exceeds 10^26
  (Theorem 1.7), by the size-rule search with `tree_below.c --eq 2,1,1,3`;
  `tree_below.py` agrees below 10^21.
- No result depends on unrefereed work. Prime factors below 2^64 in the
  eight-prime search are certified by the strong probable-prime test to the
  bases 2, …, 37 (Sorenson and Webster, Math. Comp. 2017), in place of an
  unpublished table of base-2 pseudoprimes; the rerun gives the same counts.
- Corrections to the description of the programs and the rounding analysis
  of Proposition 2.5; the value R_(10^9) of Section 6.5 is now logged.
- Shorter abstract, polished text and appendices; AI assistance is disclosed
  in one line of the data availability statement.

Author: Deep Bhattacharjee. GitHub-related contact: egspl@proton.me.
No journal submission, acceptance or full closure is asserted.
