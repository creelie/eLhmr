# Prime factors of the last defect (Section 9.9)

For a composite n = p₁⋯p_k with n − 1 = 2φ(n), let A = p₁⋯p_{k−1}, B = φ(A) and C = 2B − A, the last defect.
Then C ≥ 5, C | A − 1 and p_k = (2B − 1)/C (Proposition 9.10). If a prime ℓ divides C, then ℓ is not among
p₁, …, p_{k−1} and none of them is 1 modulo ℓ (Lemma 9.12). An *ℓ-set* of size K is an independent set S of K
primes ≥ 5, none equal to ℓ or 1 modulo ℓ, with ∏_S p/(p−1) < 2 < ∏_S p/(p−1) · q_S/(q_S − 1), where q_S is the
least prime above max S that is not 1 modulo an element of S; k_ℓ is the least K + 1 for which one exists.

Results (both programs agree on every line):

* k₅ = 201, k₇ = 58, k₁₁ = 14, k₁₃ = 21, k₁₇ = 16, k₁₉ = 15, k₂₃ = 14, k₃₇ = 12, and k_ℓ = 11 for the other
  primes 29 ≤ ℓ ≤ 199 (Proposition 9.13).
* For each pair (ℓ, k) of Table 10 every ℓ-set of size k − 1 is listed and the equation decided exactly: none
  has ℓ | C and C | A − 1 (Proposition 9.14).
* Hence ℓ | C needs at least 201, 59, 17, 24, 20, 19, 18 prime factors for ℓ = 5, 7, 11, 13, 17, 19, 23, and the
  last defect of a solution with sixteen prime factors has no prime factor below 29 (Corollary 9.15).

| file | purpose |
|---|---|
| `defect_bound.py` | first program: the search for ℓ-sets (table of primes below 3·10⁷, bounds in double precision with a margin, exact rational test of every set of full size); `python3 defect/defect_bound.py l [Kmax] [margin]` |
| `defect_scan.py` | k_ℓ for every prime ℓ in a range; `python3 defect/defect_scan.py 5 199 210 [margin]` |
| `defect_leaves.py` | lists every ℓ-set of size k − 1 and decides n − 1 = 2φ(n) on each; `python3 defect/defect_leaves.py l k` |
| `defect.gp` | second program, written separately in PARI/GP: candidates by `nextprime` (no table), bounds from the parent's candidates, 38-digit logarithms with exact rational arithmetic near ties |
| `runs.gp` | the recorded runs of `defect.gp`: `cd defect && gp -q defect.gp runs.gp < /dev/null > logs/gp_runs.log` |
| `logs/scan.log`, `logs/scan_margin6.log` | k_ℓ for 5 ≤ ℓ ≤ 199 from the first program, with the margins 10⁻⁹ and 10⁻⁶ |
| `logs/leaves.log` | the ℓ-sets of Table 10 from the first program |
| `logs/gp_runs.log` | k_ℓ and the ℓ-sets of Table 10 from the second program |

Run the Python programs from the repository root; they need `sympy`. Setting up the table of primes takes about
25 seconds.
