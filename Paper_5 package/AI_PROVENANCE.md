# AI provenance - A certified sixteen-prime-factor lower bound for Lehmer's totient problem

Human authors: Deep Bhattacharjee.
Submitting contributor: Deep Bhattacharjee, ORCID 0000-0003-0466-750X.

Text classification: A mix of human-written and AI-generated.
Human-understanding declaration: Author selection pending for the added research material; the earlier archived manuscript had the all-parts confirmation.
Basis: The user confirmed the earlier manuscripts. No new confirmation for this pass's added material is inferred. This is the submitting user's
declaration, not a claim that the assistant independently verified human understanding.

Claude through Claude Code assisted the original search programs, computational development, partial Lean work and drafting. OpenAI Codex assisted the ceiling and one-candidate reductions, targeted valuation and residue investigations, independent primality certificates, checking the stated finite reproductions, figures, editing and packaging. These efforts do not provide a full-conjecture proof. In this revision, Codex assisted the uniform factor-count construction, its proof, explicit-stack implementation, exact controls, title revision and submission files. The new appendix is supplied for author review and is not claimed as a full-conjecture proof.

Documented tools: Anthropic Claude / Claude Code; OpenAI Codex; Python; PARI/GP; Lean 4 (partial results); LaTeX / pdfLaTeX. Exact historical model versions
are not inferred from tool names. The preprint's provenance and manuscript
disclosure remain the primary account of those historical contributions.

Verification scope: The repository contains partial Lean results for statements not depending on the exhaustive search. The full searches and the full Lehmer conjecture are not claimed to be Lean-formalised. The new uniform construction has a written proof and fresh exact controls; it is not Lean-formalized. The guarded k=14 run is explicitly incomplete.

The author retains responsibility for the final mathematics, citations and
approval of the manuscript. AI systems are not added as human contributors.
The package creation step prepared source archives, submission metadata,
unsent cover letters and author-prepared AI declarations; it did not submit
the manuscript to a journal or Hexagon. Source files and figures retain their
attribution. No private prompts, unpublished chat history or hidden reasoning
traces are included or represented as an exported transcript.

Earlier preprint: https://hexagonmath.org/2610.00454v1
Research manuscript/source DOI: https://doi.org/10.5281/zenodo.23629631
Repository: https://github.com/creelie/eLhmr

## Current release 1.8.0

The manuscript and sixteen-factor result are unchanged. This release archives the subsequent ten-statement Lean verification of the exact fixed-count reduction, actual totient-factorisation bridge, final-entry identities and deficit-one exclusion. Universal emptiness for all factor counts remains unproved.

Ten additional statements in lean/UniformFinite.lean passed a fresh local Lean 4.34.1 check with only standard axioms. They prove the specified reduction and identities, not all-k emptiness or every line of the Python DFS. The older finite-search and manuscript scopes remain as recorded.
New or consolidated material awaits author review.
