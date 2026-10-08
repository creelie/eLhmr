**Lehmer's totient problem with fewer than sixteen prime factors**
Deep Bhattacharjee

A composite number n whose totient divides n − 1 was known to have at least
fourteen prime factors. The paper proves that it has at least sixteen, at
least 16001 if (n − 1)/φ(n) ≥ 3, and more than 10⁸ if 3 | n, and that
n < 2^(2^(k−7)) if n has k prime factors. For the companion equation
φ(n) | n + 1 the nine known solutions are the only ones with at most eight
prime factors, and a further solution prime to 3 has at least sixteen. By
the large sieve, the number of prime factors of a solution of either
equation is at least doubly exponential in the quotient (n ± 1)/φ(n).

Lehmer's totient conjecture remains open and is not claimed. Remark 9.16 of
the paper states the assertion about finite sets of primes that would
settle it.

### What is proved by hand and what rests on a computation

Section 1.3 of the paper sorts the results. The large-sieve theorem, the
sharp product lemma, the bound n < 2^(2^(k−2)), the extension theorem and
the structural results of Section 9 are proved entirely by hand. The bounds
16, 16001 and 10⁸, the bound n < 2^(2^(k−7)) and the list for eight prime
factors are each reduced by hand to a finite search, which at least two
independently written programs carry out with the same counts.

### Files

* `lehmer-totient.pdf`: the paper (60 pages, amsart)
* `lehmer-totient-tex.zip`: LaTeX source with the figures as PNG and their
  TikZ sources
* `lehmer-totient-arxiv.tar.gz`: LaTeX source with the figures as PDF

### Verification

`scripts/fast_checks.sh` re-runs the quicker programs and compares their
output with the recorded logs; CI runs it on every pull request together with
the Lean 4 build (Mathlib v4.34.1) and its axiom audit, which allows only
`propext`, `Classical.choice` and `Quot.sound`. The long searches (fifteen
primes, eight primes, independent sets) are archived with their logs and
data.

Earlier versions of the programs are archived at
[doi:10.5281/zenodo.23072268](https://doi.org/10.5281/zenodo.23072268).
