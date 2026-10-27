# Research release v1.10.0

A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria

The full Lehmer totient conjecture remains unproved. This release enlarges
three finite-search results of the paper:

- every composite solution of φ(n) | n−1 exceeds 10^35 (Theorem 1.3), by the
  tree search of Section 3 with a size rule (Section 5.3); the two programs
  agree below 10^31 for sixteen prime factors and below 10^32 for more, and
  the search below 10^35 was run by the C program in parts;
- a quotient (n−1)/φ(n) ≥ 3 forces at least 18001 prime factors and 3 | n
  forces more than 10^9 (Theorems 1.1 and 1.5), each by two programs;
- the size bounds n < 2^(2^(k−17981)) and n < 2^(2^(k−10^9)) (Theorem 1.2).

The programs and logs are in `tree_below.c`, `tree_below.py`,
`logs/tree_below/`, `bound/independent.c`, `bound/independent_list.c` and
`bound/logs/`. The results of v1.9.0 are retained. Deep Bhattacharjee is the
sole manuscript author; earlier creators retain their bibliography credit.

Original preprint: https://hexagonmath.org/2610.00454v1 . No replacement
identifier, journal submission, journal acceptance or full closure is asserted.
