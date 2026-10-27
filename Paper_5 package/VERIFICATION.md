# Verification scope

The supplied article retains the historical finite-search results and their
recorded verification scope. No fresh full k=15, companion-eight or
100-million-prime computation was performed in preparing this revision.
Those historical statements retain their archive references and limitations.

Fresh preparation checks:

- Three pdfLaTeX passes for the manuscript, cover letter and AI declaration.
- Undefined-reference and overfull-box checks on the final compilation logs.
- Exact integer/rational replay of the pivot-lemma counterexample in research/.
- Eight exact polynomial/integer checks of the displayed final-prime and two-tail identities, using Python standard-library arithmetic.
- Inspection of the final-prime and two-tail derivations written in the new appendix.
- PDF visual review recorded separately in build-verification.json.

No fresh complete Lean build is claimed. The new appendix is not represented
as Lean-formalised. The historical v1.8.0 check of ten UniformFinite.lean
statements is narrower than verification of all algorithms or the full conjecture.

The final-prime exclusion for every support and the full Lehmer conjecture
remain unproved. No release asset or archival DOI certifies an unproved theorem.


## Publication checks and source-ZIP rebuild

Before release, all five checks passed on source checkpoint
a56dbae7bfe419a28073679c37eac04011c66d57: research controls, revision certificates,
document compilation, Python/PARI checks, and Lean proofs/axiom audit.
This is CI coverage of the repository's specified programs and existing
Lean statements, not a formal proof of the full conjecture or the new
appendix. The historical largest search ranges retain their stated
reproduction scope.

Both final source ZIPs were extracted and compiled with three pdfLaTeX
passes. Page counts and complete extracted PDF text match the supplied
manuscript and cover letter. ZIPs were created after verification of
the published DOI 10.5281/zenodo.23680044.
