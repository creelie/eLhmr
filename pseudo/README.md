# Pseudo-solutions prime to 3

Programs and logs for Section 9 of the paper: Theorems 9.3 and 9.5, the first-moment count of Section 9.6, the check of Lemma 9.8 in Section 9.7 and the searches with prime entries of Section 9.8. The Lean
proofs of Lemma 9.2 and Proposition 9.4 are in `lean/LehmerTotient/Barrier.lean`.

The equation is

    x_1 x_2 ... x_k + eps = 2 (x_1 - 1)(x_2 - 1) ... (x_k - 1),        eps = -1 (Lehmer) or +1 (companion),

in odd integers 5 <= x_1 < ... < x_k, none divisible by 3, prime or not. Theorem 9.3 states that there is no solution
with k <= 13, and none with k <= 15 in which x_1, ..., x_{k-3} are prime. Each part is checked by two programs for
k <= 12; the case k = 13 of the first part is carried out by `integer_tree_scan.py`.

## Requirements

Those of the repository (Python 3, `sympy`, `python-flint`, `gmpy2`), a C compiler with GMP, and PARI/GP (`gp` on the
PATH) for the two `pari_*` programs. Build the C program first, in this directory:

    gcc -O2 -o tail3 tail3.c -lgmp -lm

## Files

| file | purpose | runtime |
|---|---|---|
| `tail3.c` | the last three entries for a whole interval of x_{k-2} (prime or integer), by the sum route of Section 4.4 | – |
| `tail3lib.py` | driver for `tail3`; problems where the sum route would be long are solved by a complete factorisation, with every prime factor proved prime | – |
| `integer_tree.py` | Theorem 9.3 (i), first program: the tree with integer entries prime to 3, k <= 12, both signs | seconds |
| `prime_prefixes.py` | Theorem 9.3 (ii), first program: the prime prefixes of the search of Theorems 1.1 and 1.4, then three integer entries | about 4 min of CPU time per sign for k = 15 |
| `integer_tree_scan.py` | Theorem 9.3 (i) for k = 13, both signs: the tree of `integer_tree.py`, and at depth 10 the program `scan3` of `../companion8` in its mode for odd integers prime to 3, with PARI/GP for the values where the sums would be slow; resumable through `../data/pseudo/integer_tree_k13_*.jsonl` | about 15 h of CPU time per sign, 3.8 h on 4 cores |
| `pari_integer_tree.py` | Theorem 9.3 (i), second program: its own bounds and tree, and at every node with two entries left a complete factorisation with PARI/GP, every factor proved prime; no code shared with the rest of the repository | about 10 min for k = 12 |
| `pari_prime_prefixes.py` | Theorem 9.3 (ii), second program, for k <= 14: the same prime prefixes, its own range for x_{k-2}, and a complete factorisation for every value | about 15 min per sign for k = 14 |
| `validate_with3.py` | with the entry 3 allowed, `tail3` finds exactly the solutions listed by `pari_integer_tree.py --with3` whose first k - 3 entries are prime (k <= 7, both signs) | minutes |
| `validate_prime_mode.py` | `tail3` in prime mode treats the 33,865,004 values of p_13 of the case k = 15 (`logs/k15_run_*.log`) and finds no completion | 1 min per sign |
| `first_moment.py` | the first-moment count of Section 9.6; the calibration with the entry 3 allowed | seconds (k <= 6), minutes (k = 7) |
| `first_moment_node.py` | the count for solutions prime to 3 over the tree for k = 12, and below the prefix (5, 7, 13, 17, 19, 23, 25, 37, 119) for k = 12, 13, 14 | about 5 min |
| `make_seeds.py` | the seeds of `descent.py`: every prefix of length 6 or more of the tree for k = 13, with its defect | seconds |
| `descent.py` | the search that found `companion_k25.txt`: descent through the defects with selection, testing every node for a last entry | 2.2 h on 4 cores |
| `coprime_tree.py` | the tree of `integer_tree.py` restricted to pairwise coprime entries, down to depth k - 3; collects every prefix with 0 < c x_j < 2B, which one more entry can complete (Section 9) | 1 s for k = 15 |
| `descent_coprime.py` | `descent.py` restricted to pairwise coprime entries: every child must also be prime to every earlier entry and completable by one more entry, and the threshold keeps the beam full; started from the 13190 prefixes of `coprime_tree.py 15`, the sum of 1/c falls by about a factor 0.8 per step and no completion occurs in twelve steps (Section 9) | 3 min on 3 cores |
| `prime_seeds.py` | the 12170 prefixes of `coprime_tree.py 15` that consist of primes p_1 < ... < p_j with p_i not dividing p_l - 1, with their sum of 1/c, 7.6e-11 of the 7.7e-11 of all 13190 (Section 9.8); writes `prime_prefixes_k15.pkl` | seconds |
| `descent_prime.py` | `descent.py` with every new entry a probable prime (BPSW) that is not 1 modulo an earlier entry, keeping exactly the N prime children with the smallest defect and testing every node for a last entry (2B + eps)/c; from `prime_prefixes_k15.pkl` with N = 5000 the smallest defect rises from 1.2e11 to 2.2e18 and the sum of 1/c falls from 7.6e-11 to 2.1e-18 in eight steps, with no completion (Section 9.8). `descent.py` run from the same prefixes with N = 5000 sees the sum rise, to a total of 1.9e-8 after twelve steps | 30 s on 4 cores |
| `companion_k25.txt` | a pseudo-solution prime to 3 with 25 entries and eps = +1, one entry per line | – |
| `check_tuple.py`, `check_gp.sh` | independent checks of a pseudo-solution in Python and in PARI/GP: equation, order, oddness, 3 divides no entry, all gcd(x_i, x_j - 1) = 1 | seconds |
| `fermat_k25.py` | for every entry x of `companion_k25.txt`, whether 2^(A+1) = 1 (mod x), with A the product of the entries; for the entries below 10^13 also the factorisation, squarefreeness and the primes q with q - 1 not dividing A + 1 (Lemma 9.8) | 20 min |
| `logs/` | recorded output | |

## Commands of the recorded runs

Run from this directory.

    python3 integer_tree.py 12                                          > logs/integer_tree.log
    python3 integer_tree_scan.py 13 -1 4    > logs/integer_tree_k13_m1.log    (and 13 1 4: _p1)
    for k in $(seq 3 14); do for e in -1 1; do python3 prime_prefixes.py $k $e; done; done   > logs/prime_prefixes_k3_14.log
    python3 prime_prefixes.py 15 -1 P 4    (P = 0, 1, 2, 3, and the same for eps = 1)   > logs/prime_prefixes_k15.log
    for k in $(seq 3 12); do python3 pari_integer_tree.py $k -1; done  > logs/pari_integer_tree_m1.log   (and 1: _p1)
    for k in $(seq 3 7); do for e in -1 1; do python3 pari_integer_tree.py $k $e --with3; done; done   > logs/pari_integer_tree_with3.log
    for k in $(seq 3 13); do for e in -1 1; do python3 pari_prime_prefixes.py $k $e; done; done   > logs/pari_prime_prefixes_k3_13.log
    python3 pari_prime_prefixes.py 14 -1; python3 pari_prime_prefixes.py 14 1                > logs/pari_prime_prefixes_k14.log
    for k in $(seq 3 7); do for e in -1 1; do python3 pari_prime_prefixes.py $k $e --with3; done; done   > logs/pari_prime_prefixes_with3.log
    python3 validate_with3.py                                           > logs/validate_with3.log
    python3 validate_prime_mode.py -1; python3 validate_prime_mode.py 1 > logs/validate_prime_mode.log
    python3 first_moment.py K -1 --with3 --W0 100000   (K = 4, 5, 6)
    python3 first_moment.py 7 -1 --with3 --W0 1000 --reps 20            > logs/first_moment_with3.log
    python3 first_moment_node.py 1000 30 30 --tree                      > logs/first_moment_node.log
    python3 make_seeds.py; python3 descent.py --N 10000000 --gens 16 --workers 4 --q 1.6   > logs/descent.log
                                                       (the log is kept up to step 14, where the tuple was found)
    python3 coprime_tree.py 15 > logs/coprime_tree_k15.log; python3 descent_coprime.py --N 1000000 --gens 12 --workers 3   > logs/descent_coprime.log
    python3 prime_seeds.py > logs/prime_seeds.log
    python3 descent_prime.py --seeds prime_prefixes_k15.pkl --N 5000 --gens 8 --workers 4   > logs/descent_prime.log
    python3 descent.py --seeds prime_prefixes_k15.pkl --N 5000 --gens 12 --workers 2 --out tmp/descent_int_prime_seeds.pkl   > logs/descent_int_prime_seeds.log
    python3 check_tuple.py companion_k25.txt 1; ./check_gp.sh companion_k25.txt 1
    python3 fermat_k25.py companion_k25.txt > logs/fermat_k25.log

The first-moment counts are heuristic: they estimate how many solutions to expect, and prove nothing.

## Pseudo-solutions prime to 3 for every k >= 25 (Theorem 9.5)

Write A = x_1 ... x_j, B = (x_1 - 1) ... (x_j - 1) and c = 2B - A for a prefix. Appending x gives the defect
cx - 2B, so the children of a prefix have defects r0 + ic with r0 = (-2B) mod c. A prefix with 0 < c x_j < 2B and 3 | B is
completed by one more entry exactly when c divides 2B + eps; the entry is then (2B + eps)/c, and it satisfies every
condition. `descent.py` keeps, at each step, the 10^7 admissible children with the smallest defect and tests each of
them. At step 14 the prefix with 24 entries and defect 29 closes with eps = +1, which gives `companion_k25.txt`.

The Lean files `PseudoExtend.lean` and `PseudoData.lean` check this tuple in the kernel and prove the extension:
appending 2B + 1 keeps eps = +1, and appending A gives eps = -1. So there are pseudo-solutions prime to 3 with
eps = +1 for every k >= 25 and with eps = -1 for every k >= 26. Some entries are composite (25, 119 = 7 * 17), so
none of these is a solution of Lehmer's problem or of the companion problem.

By Lemma 9.8, an entry x with a^(A+eps) = 1 (mod x) for every a prime to x, which every prime entry satisfies, is squarefree
with q - 1 dividing A + eps for each prime q | x. `logs/fermat_k25.log` shows that this fails for every composite entry of
`companion_k25.txt` except 119: 25 is not squarefree, 147563 = 13 * 11351 and 45571237 = 17 * 2680661 fail at 11351 and
2680661, and the fourteen larger entries have 2^(A+1) != 1 (mod x).
