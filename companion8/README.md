# The companion equation with eight prime factors

Programs and logs for Section 7.4 of the paper: φ(n) | n+1 has no solution with exactly eight prime factors, which
completes Theorem 1.3 (the solutions with at most eight prime factors are the nine known ones).

By Lemmas 2.1–2.3 and Theorem 1.4 such a solution satisfies n + 1 = 2φ(n) and n = 3·p₂⋯p₈. The search of Section 3
is run with p₁ = 3 down to depth 5, which gives 10458 prefixes (3, p₂, …, p₅) with their intervals for p₆. For every
admissible prime s = p₆ in these intervals the last two primes p < q satisfy

    (c p − 2B')(c q − 2B') = N,    A' = A s,  B' = B (s − 1),  c = 2B' − A',  N = 2A'B' + c,

so t = c p − 2B' is a divisor of N in one residue class modulo c (Proposition 4.1). `scan3` finds these divisors by
trial division below a split point t_d and, above it, by running the sum σ = p + q over its class modulo 6c and testing
whether σ² − 4pq is a square (Section 4.4). Both loops are sieved by congruences that primes p, q > s satisfy. When
this would take longer than a complete factorisation of N (about 4 ms), `scan3` passes s to `factor_class.gp`, which
factors N with PARI/GP, proves every prime factor prime (`factor_proven = 1`) and lists the divisors in the class.

## Requirements

A C compiler and GMP (`gcc -O3 -march=native -o scan3 scan3.c -lgmp -lm`; the Python drivers compile it when needed),
PARI/GP 2.15 or later (`gp` on the PATH), Python 3 with `sympy` and `gmpy2`, and `lastthree.py` from the repository
root (for the frontier).

## Files

| file | purpose | runtime |
|---|---|---|
| `scan3.c` | the last three entries for a whole interval of s: trial division and sums, sieved; every completion is checked with GMP before it is printed | – |
| `factor_class.gp` | the fallback: complete factorisation of N, every prime factor proved prime, all divisors in the class | – |
| `common.py` | helpers shared by the drivers: running `scan3` and `factor_class.gp`, exact check of a completion | – |
| `test_scan3.py` | the tests of Appendix A.8: known solutions for k ≤ 7, the odd-integer counts 1, 1, 2, 8, 47 and 1, 1, 2, 4, 18, each by four routes, 2868 pairs (prefix, s) of the case k = 8 and 600 values of x₁₁ per sign of the case k = 13 of Theorem 9.3 against complete factorisation | about 3 min |
| `companion8.py` | the search: 10897 pieces in 445 batches, resumable through the journal `data/companion8/journal.jsonl` | 6.9 h of CPU time, 2.0 h on 4 cores |
| `recheck.py` | a random sample of the pieces, and every piece with a completion, run again with other weights and another factoring threshold; counts and completions must agree with the journal | minutes |
| `logs/` | recorded output | |

## Commands of the recorded runs

Run from the repository root.

    python3 companion8/test_scan3.py              > companion8/logs/test_scan3.log
    python3 companion8/companion8.py 4            > companion8/logs/companion8.log
    python3 companion8/recheck.py 0.03 4          > companion8/logs/recheck.log

The same program, in its mode for odd integers prime to 3, carries out the case k = 13 of Theorem 9.3 (i)
(`pseudo/integer_tree_scan.py`).
