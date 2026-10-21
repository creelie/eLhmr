Dear Editor,

I submit the manuscript "Lehmer's totient problem with fewer than sixteen prime factors" for
consideration by the International Journal of Number Theory.

Lehmer asked in 1932 whether a composite n can satisfy phi(n) | n-1. The best refereed bound was
Cohen and Hagis's fourteen prime factors (1980); fifteen was announced by Renze and by Pinch
without a refereed proof. The paper proves that a composite solution has at least sixteen
distinct prime factors, at least 16001 when (n-1)/phi(n) >= 3 and more than 10^8 when 3 | n, and
that a solution with k prime factors is below 2^(2^(k-7)), which divides the number of binary
digits allowed by the bound of Burek and Zmija by 128. For the companion equation phi(n) | n+1 it
proves that the nine known solutions are the only ones with at most eight prime factors and that
a further solution prime to 3 has at least sixteen, the first refereed bounds for that equation.
The new ingredient is a treatment of the last three prime factors together, as a divisor of an
explicit integer in a residue class found by lattice reduction or by a short scan of a fixed
sum, which reduces the case of fifteen primes to a quarter of an hour of computation.

Each statement is reduced by hand to a finite computation, and every computation was carried out
by at least two independently written programs, one of which never factors an integer, so that
its negative answers depend on no primality proof; the programs were also run on an equation with
known solutions, listed in Appendix A. The programs, their recorded output and Lean 4 proofs of
the statements that do not depend on a search are public in release v1.4.0,
https://github.com/creelie/eLhmr/releases/tag/v1.4.0.
The paper does not claim Lehmer's conjecture; its closing proposition states the assertion
equivalent to it and the constraints on its divisor that the algebra gives.

The manuscript is 44 pages with 18 figures. It was submitted earlier to the Journal of Number
Theory and to Mathematics of Computation and was not accepted there; it is not under
consideration elsewhere. The use of an AI tool in writing the programs and the Lean proofs and
in drafting text is declared at the end of the manuscript; I reviewed and edited all of it and
take full responsibility for the content. MSC 2020: primary 11A25; secondary 11A41, 11A51,
11D68, 11N36, 11Y11, 11Y16, 11Y70. Keywords: Lehmer's totient problem, Euler's totient function,
large sieve, Fermat primes.

Yours sincerely,

Deep Bhattacharjee
itsdeep@live.com, ORCID 0000-0003-0466-750X
