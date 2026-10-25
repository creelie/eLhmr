# A certified sixteen-prime-factor lower bound for Lehmer's totient problem

Paper 5. Author byline: Deep Bhattacharjee.
Selected journal: Mathematics of Computation. This is a prepared package, not a submission.

For Hexagon or Overleaf, upload **A_certified_sixteen_prime_factor_lower_bound_for_Lehmers_totient_problemtex.zip**, choose main.tex and pdfLaTeX.
The reference PDF is **A_certified_sixteen_prime_factor_lower_bound_for_Lehmers_totient_problem.pdf**. All required figures and bibliography files
are included; Lean sources are linked separately. Do not upload this entire
package folder as the article source: it also contains correspondence and AI
provenance. Read hexagonsubmissionform.md for the complete portal fields, and
upload AI_PROVENANCE.md in Hexagon's separate AI-provenance field.

Journal files: coverletterjournal.pdf, coverlettertex.zip,
journalaideclarationform.pdf and journalsubmissiondetails.md. The declaration
is author-prepared, not an official publisher form or a signed document.
No PDF has row or margin line numbering.

Manuscript/source archive: https://doi.org/10.5281/zenodo.23629631
Existing preprint: https://hexagonmath.org/2610.00454v1
The new package release DOI is recorded only after its public record is
verified. Package manifests distinguish archive content from later DOI receipts.

Read RESEARCH-STATUS.md before using the submission files.

## Latest package revision v1.8.0

The manuscript and sixteen-factor result are unchanged. This release archives the subsequent ten-statement Lean verification of the exact fixed-count reduction, actual totient-factorisation bridge, final-entry identities and deficit-one exclusion. Universal emptiness for all factor counts remains unproved.

Formal verification scope: Ten additional statements in lean/UniformFinite.lean passed a fresh local Lean 4.34.1 check with only standard axioms. They prove the specified reduction and identities, not all-k emptiness or every line of the Python DFS. The older finite-search and manuscript scopes remain as recorded.

The current package DOI will be added only after Zenodo confirms publication. Earlier manuscript/source DOIs above are historical citations.


Confirmed research archive: https://doi.org/10.5281/zenodo.23638948
Release: https://github.com/creelie/eLhmr/releases/tag/v1.8.0
The receipt was added after the immutable source checkpoint. See ARCHIVE-DOI.md and RESEARCH-STATUS.md.
