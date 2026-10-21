# AI provenance statement

Manuscript: "Lehmer's totient problem with fewer than sixteen prime factors", Deep Bhattacharjee.

Claude (Anthropic), through Claude Code, was used to write and run the search programs, to write
the Lean 4 proofs of the statements that do not depend on a search, and to draft text. The author
directed the work, reviewed and edited all of it, and takes full responsibility for the content.
No AI system is an author.

Every statement of the paper is proved in the text or reduced by hand to a finite computation
whose programs, recorded output and Lean proofs are public in release v1.4.0 of the code,
https://github.com/creelie/eLhmr/releases/tag/v1.4.0. Each computation was carried out by
two independently written programs, one of which never factors an integer, and the programs were
exercised on an equation with known solutions (Appendix A). No result rests on an AI output that
was not checked in this way. The same disclosure is made in the Data and code availability
section of the manuscript.
