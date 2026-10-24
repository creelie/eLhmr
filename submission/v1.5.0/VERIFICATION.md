# Verification account

Base source commit: fd398ef410faeca431c3c5bab142f3443e857cdf.
All fresh executions took place on 24 October 2026, Windows.

## Freshly executed

1. k=15, both signs, program C (separate runs): all 55,443 expected tasks completed once,
   and the frontier was regenerated from the source. All 33,865,004 admissible
   p13 values per sign were treated, with zero integer candidates and zero prime solutions.
   The receipt verifies the exact task set, not just the number of records.
2. k=7..14 for both signs, program C: recorded counts agree; all 61 known
   positive-control completions recovered.
3. Divisor routine: 3,100 independently factored random/planted instances,
   including 1,610 planted divisors; zero mismatches.
4. Exact threshold products, one-/two-prime extensions, all fifteen stored
   k=14 factorisation certificates and hand-bound computations rerun.
5. Exact s=7 size search: 33,678 nodes, maximum depth 13, 14,814 last-prime
   tests, 1,418 light nodes, zero Lehmer numbers, matching the archived count.
6. New one-candidate code: 6,475 prefixes; 537,786 prime-tail comparisons
   across both signs; six known companion solutions recovered; composite
   Fermat-tail negative control rejected.
7. Relaxed-equation barrier: independently multiplied the supplied 25-entry
   plus-sign tuple and its 26-entry minus-sign extension; all cross-gcd
   conditions hold. The entry 25 demonstrates that these are not prime tuples.

## Archived-data checks and CI

The six saved k=15 implementation runs were compared task by task. They agree.
This comparison is not presented as a fresh execution of all six runs.
Existing upstream GitHub CI at the pinned base commit reports success for
Python/PARI checks, Lean/axiom audit, and the paper build. The exact public
check metadata is saved in verification/upstream-check-runs.json.

No new complete Lean build was run. The written proof in the new subsection
has not been formalised. The exhaustive searches are not formalised by the
upstream project either. No standard-kernel proof of the full conjecture exists
in this package.

The independent-set computations with 10^8 primes and the eight-prime
companion search were not rerun here; their archived results are retained
with that explicit distinction. This is not a claim of a new independent
verification of every result in the original article.

## PDF

Built with TeX Live 2023. See verification/pdf-qa.json for final page count,
rendered-page inspection status and diagnostics. The only retained class
warning is the installed cmtiup package's self-reported package-name mismatch.
No margin line numbering is enabled. The mathematical statement of the
remaining all-prefix obstruction is not changed into a proved theorem.

The five deterministic Anaxia Lehmer tests also passed. Its current public head
matched the inspected commit. No model subagents or proposer calls were run.
The desktop editor compiler passed after an engine-conditional microtype fix;
the delivered PDF was built and inspected independently with pdflatex.

All 41 distinct stored k=14 factors were additionally proved prime by complete
Lucas certificates (259 recursive prime nodes). The standard-library verifier
checked all 15 recomputed factorizations and the exact set of root factors.
The source and complete criterion proof are included. This closes a finite
verification issue beyond the original probable-prime range.

The additional valuation attempt proves its proposed multiplicity filter is
algebraically redundant after exact divisibility. Its 6,475-prefix consistency
check passed; this supplies no new general exclusion. See VALUATION-ROUTE.md.
