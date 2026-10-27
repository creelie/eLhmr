# Lehmer's totient problem: the exact final-prime obstruction

27 October 2026. Research audit, not a proof of the full conjecture.

## The statement that remains to be proved

Let S be a nonempty finite set of distinct odd primes, and put

\[
A=\prod_{p\in S}p,\qquad B=\prod_{p\in S}(p-1)=\varphi(A),
\qquad r=\max S.
\]

If a further prime q>r gives a Lehmer counterexample Aq, write

\[
Aq-1=M B(q-1),\qquad M\ge2.
\]

Rearrangement gives the exact identity

\[
Dq=MB-1,\qquad D=MB-A,\qquad D(q-1)=A-1.
\]

Here D>0. Also

\[
0<M-\frac AB=\frac{A-1}{B(q-1)}<\frac12.
\]

For completeness, the last inequality follows without any factor-count bound:
the primes of S form a subset of {3,...,r}, and all factors j/(j-1)>1, so

\[
\frac AB=\prod_{p\in S}\frac p{p-1}
\le\prod_{j=3}^{r}\frac j{j-1}=\frac r2
<\frac{q-1}{2}.
\]

Consequently M=ceil(A/B). Conversely, for any such S, if

\[
M=\left\lceil\frac AB\right\rceil,\quad D=MB-A>0,
\quad D\mid A-1,\quad q=1+\frac{A-1}{D}>r
\]

and q is prime, then Aq is composite and satisfies
\(\varphi(Aq)\mid Aq-1\). (A/B>1 gives M>=2.)

Thus the required universal assertion is precisely that no S satisfies all of
these conditions. The identities do not by themselves show that q is composite.
No argument in this audit proves that universal assertion. No earlier finite
factor-count searches were rerun for this audit.

## Why deleting the largest prime cannot give an induction

Suppose a Lehmer counterexample Aq existed with q its largest prime. The
preceding bound says 0<D<B/2. Since A is odd and B is even, D is a positive odd
integer and B is an even integer greater than 2. Hence D+1<=B/2<B. It follows
that

\[
\frac{A-1}{B}=M-\frac{D+1}{B},\qquad
M-1<\frac{A-1}{B}<M.
\]

In particular B does not divide A-1. Removing the largest prime cannot produce
a smaller Lehmer counterexample, even if its integer quotient is allowed to
change. This is an obstruction to that particular descent operation, not to
all possible descent arguments. A successful descent must specify a different
map and prove preservation of the arithmetic equation and primality.

## A checked obstruction to a proposed uniform pivot descent

Source: Daniel Sautot, *Lehmer's Totient Problem and a Prime-Cost Pivot Method*,
March 2026, Zenodo DOI 10.5281/zenodo.18911153,
https://zenodo.org/records/18911153. The downloaded 75-page PDF was inspected
visually on pages 19 and 34. This section concerns Lemma 6.40 **as stated**.
It does not claim a counterexample to Lehmer's conjecture.

The paper defines

\[
n_T=\prod_{p\in T}p,\quad L(T)=\operatorname{lcm}_{p\in T}(p-1),
\quad P(T)=\frac{\log L(T)}{\log n_T},
\quad R_T(p)=\frac{L(T)}{L(T\setminus\{p\})}.
\]

Its fixed parameters are

\[
\varepsilon_B=\frac25,\qquad
h(y)=y^{2/5-1/(3(\log y)^4)},\qquad
\delta_B(y)=\frac1{3(\log y)^4}>0.
\]

Lemma 6.40 claims that, for any finite odd-prime support T with min(T)=y,
|T|>=2, P(T)<=3/5, and p>y with R_T(p)<=h(y), removing p increases P by at
least delta_B(y). Its displayed statement does not assume that n_T satisfies
the paper's admissibility congruences.

Take

\[
T=\{7,11,13,19,31,151,251,271,751,2251\},\qquad p=13.
\]

Every listed integer is prime. Exact multiplication and lcm calculation give

\[
n_T=10237284291923908219,\quad L(T)=13500,
\quad L(T\setminus\{13\})=6750,\quad R_T(13)=2.
\]

This support also satisfies gcd(n_T,phi(n_T))=1. We do **not** claim that it
satisfies the stronger admissibility hypotheses used elsewhere in the paper.

The lemma's numerical hypotheses hold. Indeed n_T>13500^4, so P(T)<1/4<3/5.
Also h(7)>2. An elementary verification of the latter uses
19/10<log(7)<2 and log(2)<7/10:

\[
\log h(7)=\frac25\log7-\frac1{3(\log7)^3}
>\frac{19}{25}-\frac{1000}{20577}>\frac7{10}>\log2.
\]

But the exact change of potential is

\[
P(T\setminus\{p\})-P(T)
=\frac{P(T)\log p-\log R_T(p)}{\log(n_T/p)}.
\]

Its numerator is strictly negative in this example: P(T)<1/4 and
13<16 imply P(T)log(13)<log(2). Therefore

\[
P(T\setminus\{13\})<P(T),
\]

contrary even to monotonic increase, and hence contrary to the claimed
positive minimum gain. Decimal illustrations are P(T) approximately
0.2172695226 and a change approximately -0.0032970082 (the accompanying JSON gives
the computed values at 50-digit working precision).

The error is visible in the proof: from a<=c b one cannot infer a d>=c b d
for d>0. In its notation, A<=(1-epsilon_B)B gives

\[
Ab-aB\le (1-\varepsilon_B)Bb-aB,
\]

where the manuscript prints the reverse inequality. Replacing a positive
denominator by a lower bound also cannot produce the claimed lower bound.
The final equality replacing 1-epsilon_B by epsilon_B is additionally invalid
for epsilon_B=2/5.

This invalidates the stated lemma as an available input for uniform descent.
It does not establish that the main conjecture is false, nor does it rule out
a corrected lemma with substantial additional hypotheses and a new proof.

## Reproducibility and scope

Run `verify_pivot_counterexample.py` with Python 3. It checks primality by
trial division, uses exact integer multiplication and lcms, and proves the
decisive inequalities with integers and rational bounds for logarithms. The
logarithm bounds use

\[
\log x=2\sum_{j=0}^{k-1}\frac{z^{2j+1}}{2j+1}+E_k,\quad
z=\frac{x-1}{x+1},\quad
0<E_k<\frac{2z^{2k+1}}{(2k+1)(1-z^2)}.
\]

The reported Decimal logarithms are illustrative and are not assumptions in
the exact verification. This audit is not a Lean formalization. It changes no
manuscript, release or DOI. The remaining universal final-prime exclusion is
unproved here.
