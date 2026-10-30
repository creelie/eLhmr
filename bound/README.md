# Independent sets of primes and the size of a solution (Proposition 2.5 and Section 6 of the paper)

Programs and logs for Proposition 2.5 and Theorem 1.2 of the paper

> Deep Bhattacharjee,
> *A sixteen-prime-factor bound for Lehmer's totient problem and exact prime-completion criteria*.

A set of primes is *independent* if no element divides another minus 1; the prime factors of a solution of
φ(n) | n ∓ 1 form one. Proposition 2.5 states that no independent set of at most 20000 primes p ≥ 5 has
∏ p/(p−1) ≥ 2.999999, and that no independent set of at most 10^9 primes p ≡ 2 (mod 3) has ∏ p/(p−1) ≥
(8/3)(1 − 10^−6), or ≥ (10/3)(1 − 10^−6). By Corollary 2.6 a composite n with φ(n) | n−1 has at least 20001 prime
factors if (n−1)/φ(n) ≥ 3, and more than 10^9 if 3 | n (Theorem 1.1); the same holds for φ(n) | n+1 with
(n+1)/φ(n) ≥ 3 (Theorem 1.6). The searches are branch-and-bound over independent sets in increasing order; the
proof that they are complete is in the paper.

Theorem 1.2 states that a composite n with φ(n) | n−1 and k distinct prime factors satisfies
n < 2^(2^(k−7)); n < 2^(2^(k−19981)) when (n−1)/φ(n) ≥ 3; and n < 2^(2^(k−10^9)) when 3 | n.
Burek and Żmija had n ≤ 2^(2^k) − 2^(2^(k−1)). The proof of the first bound combines a sharp form of the product
lemma of Cook and Nielsen (Theorem 6.2, proved by hand) with an exhaustive search over the smallest prime factors
(Section 6.3); the other two combine the lemma of Cook and Nielsen with Proposition 2.5 (Section 6.5). The search
programs write P_j, F_j, r_j and t_i for the quantities A_j, B_j, P_j and θ_i of the paper.

| file | purpose | runtime |
|---|---|---|
| `independent.py` | Proposition 2.5(i), table of primes in memory, floating-point bounds with an exact rational fallback; `python3 independent.py 2999999/1000000 18000` (502,473 nodes, depth 54; 90,320 nodes, depth 46, for K = 16000). For K = 20000 the run is split: `--part i/4 --splitdepth 10` deals out the nodes of depth 10 in creation order, and `--sub j/16@14` deals out those of depth 14 of a part again; parts 1–3 and the sixteen subparts of part 0 (run on GitHub Actions by `.github/workflows/independent-split.yml`) create 3,130,127 sets in all, depth 63, and find none (`logs/independent_py_i_20000/`) | 63 min (10 min for K = 16000; 7.0 processor hours for K = 20000) |
| `independent_list.c` | the same search in C, with the candidate list of each node filtered from its parent's list instead of rescanning the prime table (long double sums, same MARGIN rule); `gcc -O2 -o independent_list independent_list.c -lm` and `./independent_list 18000 2999999 1000000 3000000` (502,696 nodes, depth 54: the 223 extra nodes are nodes that the floating-point bound keeps and the exact rational check of `independent.py` discards). `./independent_list 20000 2999999 1000000 3000000` creates 3,131,961 sets, depth 63, and finds none (1,834 more than `independent.py`, for the same reason) | 86 s (549 s for K = 20000) |
| `independent.c` | Proposition 2.5(ii) and (iii) in C: the same branch-and-bound over the primes p ≡ 2 (mod 3), a segmented sieve to 1.2·10^11 in place of the table, `gcc -O2 -o independent independent.c -lm`; `./independent mod3 1000000000 333333 125000 120000000000` for (ii) (19 nodes, depth 4) and `... 333333 100000 ...` for (iii) (2 nodes) | 28 min and 3 min |
| `independent.gp` | the same search written separately in PARI/GP; `printf 'K = 16000; V = 2999999/1000000; LIM = 3*10^6\n\\r independent.gp\n' \| gp -q` | 78 min |
| `independent_stream.py` | Proposition 2.5(ii) and (iii): each node streams once through the primes p ≡ 2 (mod 3), sieved in segments; `python3 independent_stream.py 1.2e11 333333/125000 1000000000` for (ii) (19 nodes, 576 s, the second program for K = 10^9) and `333333/100000` for (iii); with `2e10 ... 100000000 --cache table.npz` the runs for K = 10^8 (9 and 2 nodes) | 10 min for (ii) at K = 10^9 |
| `independent_stream.gp` | the same searches written separately in PARI/GP with `forprime`; `printf 'K = 10^9; V = 333333/100000; X = 12*10^10\n\\r independent_stream.gp\n' \| gp -q` for (iii) at K = 10^9 (2 nodes, 95 min, the second program); for K = 10^8, `K = 10^8; X = 2*10^10` | 40 min for (ii) and 8.5 min for (iii) at K = 10^8; for (ii) at K = 10^9 the run takes hours per node and was not completed |
| `search.py` | the search of Section 6.3 (tree T_s, rules R1–R4), exact rationals; `python3 search.py 7` | 25 s for s = 7 |
| `search.gp` | the same search written independently in PARI/GP, explicit stack, rule R4(iii) by bisection; `printf 's = 7\n\\r search.gp\n' \| gp -q` | 9 s for s = 7 |
| `search_probe.gp` | `search.gp` with progress output, used to probe s = 8; `printf 's = 8\n\\r search_probe.gp\n' \| gp -q`. Stopped after about 5 min at a node of depth 12 with more than 10^6 children (`logs/search_probe_s8.log`); the search for s = 8 is not complete | – |
| `search_without_deficit.py` | the search with only the ratio test (no R2, no R4(iii)); `python3 search_without_deficit.py 6` gives 4,469 nodes | 18 s for s = 6 |
| `ratio_bound.py` | the exact values R_19981 = 2.999999038530… < 3 (J = 20000; R_19982 > 3) and R_(10^9) = 3.999996068… < 4 (J = 10^9 + 1) of Section 6.5; `python3 ratio_bound.py 20000` (`16000` and `18000` give the earlier R_15981 and R_17981) | 4 s |
| `hand_bound.py` | exact check of the numbers in the proof of Proposition 6.11 (no solution is 2-heavy, so n < 2^(2^(k−2)), proved by hand) and of the remark after it (none is 1-heavy); `python3 hand_bound.py` | 1 s |
| `greedy_growth.py` | Table 1 of Section 2.2: the independent sets chosen one prime at a time, with their products against log log x; `python3 greedy_growth.py 1e8 all` and `... 1e8 mod3` | 1 min each |
| `tree_stats.py`, `tree_profile.py` | nodes and last-prime tests by depth (Table 5, Figure 14) and the ranges of Figure 13 | seconds |
| `logs/` | recorded output: `independent_py_i.log`, `independent_gp_i.log`, `independent_stream_py_ii.log`, `independent_stream_py_iii.log`, `independent_stream_gp_ii.log`, `independent_stream_gp_iii.log` (K = 16000 and 10^8), `independent_py_i_18000.log`, `independent_list_c_i_18000.log`, `independent_list_c_i_20000.log`, `independent_c_ii_1e9.log`, `independent_c_iii_1e9.log`, `independent_stream_py_ii_1e9.log`, `independent_stream_gp_iii_1e9.log`, `independent_py_i_20000/` (parts 1–3 and the sixteen subparts of part 0 for K = 20000), `ratio_bound_18000.log`, `ratio_bound_20000.log`, `search_py_s*.log`, `search_gp_s*.log` (s = 1..7), `hand_bound.log`, `greedy_growth_all.log`, `greedy_growth_mod3.log`, `ratio_bound.log`, `search_without_deficit_s6.log`, `search_probe_s8.log`, `hist_s*.json`, `prof_s7.json` | |

The five figures of Section 6 are drawn from TikZ sources in `../paper/figures` (`fig_dichotomy`, `fig_bases`, `fig_rules`,
`fig_margins`, `fig_trees`); `make_heavy.py` there writes the last two from `logs/`.

For Proposition 2.5 two programs of each pair create the same sets up to the margin: for (i) at K = 20000, 3,130,127 (Python)
and 3,131,961 (C), the largest with 63 elements; at K = 18000, 502,473 and 502,696, the largest with 54 elements (90,320 for K = 16000, 2,567 for K = 10,000 and 19,711 for K = 14,000,
logs `independent_*_i.log`, `_10000.log` and `_14000.log`); for (ii) at K = 10^9, 19 sets by `independent.c` and
`independent_stream.py`; for (iii) at K = 10^9, 2 sets by `independent.c` and `independent_stream.gp` (9 and 2 at
K = 10^8); none reaches the target. The searches below 10^35 and 10^26 of Sections 5.3 and 7.5 (Theorems 1.3 and 1.7) is in `../tree_below.c`,
`../tree_below.py` and `../logs/tree_below/`. The figures of Section 2.1 are written by `make_indep.py` and `make_products.py`
in `../paper/figures`.

For Section 6 both programs report the same trees for s = 1, ..., 7: 1, 3, 7, 12, 24, 118 and 33,678 nodes, depth 13 for
s = 7, 14,814 values of M tested for a last prime, none giving an integer. Requirements: Python 3 with `numpy`,
`gmpy2`, `sympy` and `mpmath`, PARI/GP 2.15, gcc (and GMP for `../tree_below.c`).

The programs were written by Deep Bhattacharjee with the assistance of Claude (Anthropic).
