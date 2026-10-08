# Independent sets of primes and the size of a solution (Proposition 2.5 and Section 6 of the paper)

Programs and logs for Proposition 2.5 and Theorem 1.2 of the paper

> Deep Bhattacharjee,
> *Lehmer's totient problem with fewer than sixteen prime factors*.

A set of primes is *independent* if no element divides another minus 1; the prime factors of a solution of
φ(n) | n ∓ 1 form one. Proposition 2.5 states that no independent set of at most 16000 primes p ≥ 5 has
∏ p/(p−1) ≥ 2.999999, and that no independent set of at most 10^8 primes p ≡ 2 (mod 3) has ∏ p/(p−1) ≥
(8/3)(1 − 10^−6), or ≥ (10/3)(1 − 10^−6). By Corollary 2.6 a composite n with φ(n) | n−1 has at least 16001 prime
factors if (n−1)/φ(n) ≥ 3, and more than 10^8 if 3 | n (Theorem 1.1); the same holds for φ(n) | n+1 with
(n+1)/φ(n) ≥ 3 (Theorem 1.5). The searches are branch-and-bound over independent sets in increasing order; the
proof that they are complete is in the paper.

Theorem 1.2 states that a composite n with φ(n) | n−1 and k distinct prime factors satisfies
n < 2^(2^(k−7)); n < 2^(2^(k−15981)) when (n−1)/φ(n) ≥ 3; and n < 2^(2^(k−10^8)) when 3 | n.
Burek and Żmija had n ≤ 2^(2^k) − 2^(2^(k−1)). The proof of the first bound combines a sharp form of the product
lemma of Cook and Nielsen (Theorem 6.2, proved by hand) with an exhaustive search over the smallest prime factors
(Section 6.3); the other two combine the lemma of Cook and Nielsen with Proposition 2.5 (Section 6.5). The search
programs write P_j, F_j, r_j and t_i for the quantities A_j, B_j, P_j and θ_i of the paper.

| file | purpose | runtime |
|---|---|---|
| `independent.py` | Proposition 2.5(i), table of primes in memory, floating-point bounds with an exact rational fallback; `python3 independent.py 2999999/1000000 16000` (90,320 nodes, depth 46) | 10 min |
| `independent.gp` | the same search written separately in PARI/GP; `printf 'K = 16000; V = 2999999/1000000; LIM = 3*10^6\n\\r independent.gp\n' \| gp -q` | 78 min |
| `independent_stream.py` | Proposition 2.5(ii) and (iii): each node streams once through a table of the primes p ≡ 2 (mod 3) up to 2·10^10; `python3 independent_stream.py 2e10 333333/125000 100000000 --cache table.npz` for (ii), `333333/100000` for (iii) (9 and 2 nodes) | 11 min to build the table, then 1.5 min and 15 s |
| `independent_stream.gp` | the same searches written separately in PARI/GP with `forprime`; `printf 'K = 10^8; V = 333333/125000; X = 2*10^10\n\\r independent_stream.gp\n' \| gp -q` | 40 min for (ii), 8.5 min for (iii) |
| `search.py` | the search of Section 6.3 (tree T_s, rules R1–R4), exact rationals; `python3 search.py 7` | 25 s for s = 7 |
| `search.gp` | the same search written independently in PARI/GP, explicit stack, rule R4(iii) by bisection; `printf 's = 7\n\\r search.gp\n' \| gp -q` | 9 s for s = 7 |
| `search_probe.gp` | `search.gp` with progress output, used to probe s = 8; `printf 's = 8\n\\r search_probe.gp\n' \| gp -q`. Stopped after about 5 min at a node of depth 12 with more than 10^6 children (`logs/search_probe_s8.log`); the search for s = 8 is not complete | – |
| `search_without_deficit.py` | the search with only the ratio test (no R2, no R4(iii)); `python3 search_without_deficit.py 6` gives 4,469 nodes | 18 s for s = 6 |
| `ratio_bound.py` | the exact values R_15981 = 2.99999900041… < 3 (J = 16000) and R_(10^8) = 3.9999966… < 4 (J = 10^8 + 1) of Section 6.5; `python3 ratio_bound.py 16000` | 4 s |
| `hand_bound.py` | exact check of the numbers in the proof of Proposition 6.11 (no solution is 2-heavy, so n < 2^(2^(k−2)), proved by hand) and of the remark after it (none is 1-heavy); `python3 hand_bound.py` | 1 s |
| `greedy_growth.py` | Table 1 of Section 2.2: the independent sets chosen one prime at a time, with their products against log log x; `python3 greedy_growth.py 1e8 all` and `... 1e8 mod3` | 1 min each |
| `tree_stats.py`, `tree_profile.py` | nodes and last-prime tests by depth (Table 5, Figure 14) and the ranges of Figure 13 | seconds |
| `logs/` | recorded output: `independent_py_i.log`, `independent_gp_i.log`, `independent_stream_py_ii.log`, `independent_stream_py_iii.log`, `independent_stream_gp_ii.log`, `independent_stream_gp_iii.log`, `search_py_s*.log`, `search_gp_s*.log` (s = 1..7), `hand_bound.log`, `greedy_growth_all.log`, `greedy_growth_mod3.log`, `ratio_bound.log`, `search_without_deficit_s6.log`, `search_probe_s8.log`, `hist_s*.json`, `prof_s7.json` | |

The five figures of Section 6 are drawn from TikZ sources in `../paper/figures` (`fig_dichotomy`, `fig_bases`, `fig_rules`,
`fig_margins`, `fig_trees`); `make_heavy.py` there writes the last two from `logs/`.

For Proposition 2.5 the two programs of each pair create the same sets: 90,320 for (i), the largest with 46 elements
(2,567 for K = 10,000 and 19,711 for K = 14,000, logs `independent_*_i_10000.log` and `_14000.log`), 9 for (ii) and 2
for (iii); none reaches the target. The figures of Section 2.1 are written by `make_indep.py` and `make_products.py`
in `../paper/figures`.

For Section 6 both programs report the same trees for s = 1, ..., 7: 1, 3, 7, 12, 24, 118 and 33,678 nodes, depth 13 for
s = 7, 14,814 values of M tested for a last prime, none giving an integer. Requirements: Python 3 with `numpy`,
`gmpy2`, `sympy` and `mpmath`, PARI/GP 2.15.

The programs were written by Deep Bhattacharjee with the assistance of Claude (Anthropic).
