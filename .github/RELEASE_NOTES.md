**Lehmer's totient problem with fewer than sixteen prime factors**
Deep Bhattacharjee

A composite number n whose totient divides n − 1 was known to have at least
fourteen prime factors. The paper proves that it has at least sixteen, at
least 16001 if (n − 1)/φ(n) ≥ 3, and more than 10⁸ if 3 | n, and that
n < 2^(2^(k−7)) if n has k prime factors. For the companion equation
φ(n) | n + 1 the nine known solutions are the only ones with at most eight
prime factors, and a further solution prime to 3 has at least sixteen.

Lehmer's totient conjecture remains open and is not claimed. Remark 9.16 of
the paper states the assertion about finite sets of primes that would
settle it.

### New in v1.2.0

* The account of earlier work is corrected. The bound saying that the
  number of prime factors is at least doubly exponential in the quotient
  (n ± 1)/φ(n) is due to Meijer (Math. Scand. 1974) and Yamada
  (arXiv:2303.16853); the paper now credits them and presents its
  large-sieve argument as a short proof of their result, and the abstract
  no longer lists it among the new results.
* Hagis (1988) proved ω(n) ≥ 1991 when (n − 1)/φ(n) = 3; the paper now
  says that the bound 16001 improves it, and cites Grytczuk and Wójtowicz
  (2003) for larger quotients.
* Norman (arXiv:2106.11781) claimed that (n − 1)/φ(n) ≥ 3 for every
  composite solution. The paper shows that the lemma the claim rests on
  fails, for instance for the group C₂ × C₂ × C₅, so the claim is unproved.
* The theorems, proofs and computations are unchanged from v1.1.0.

### What is proved by hand and what rests on a computation

Section 1.3 of the paper sorts the results. Meijer's bound and the
Meijer–Yamada theorem (by the large sieve), the sharp product lemma, the bound n < 2^(2^(k−2)), the extension theorem and
the structural results of Section 9 are proved entirely by hand. The bounds
16, 16001 and 10⁸, the bound n < 2^(2^(k−7)) and the list for eight prime
factors are each reduced by hand to a finite search, which at least two
independently written programs carry out with the same counts.

### Files

* `lehmer-totient.pdf`: the paper (61 pages, amsart)
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

### Citation

Concept DOI (all versions):
[10.5281/zenodo.23243779](https://doi.org/10.5281/zenodo.23243779).
Version 1.1.0: [10.5281/zenodo.23244062](https://doi.org/10.5281/zenodo.23244062).
Version 1.0.0: [10.5281/zenodo.23243780](https://doi.org/10.5281/zenodo.23243780).
