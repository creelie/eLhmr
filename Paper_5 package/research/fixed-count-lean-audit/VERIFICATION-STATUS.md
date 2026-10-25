# Lehmer: verified fixed-count reduction, full conjecture still unproved

25 October 2026. This is a working verification supplement, not a new
full-closure release. The research release remains v1.7.0,
<https://doi.org/10.5281/zenodo.23637442>.

## What the new Lean check establishes

`lean/UniformFinite.lean` defines a counterexample using the ordinary
Euler totient, ordinary primality, and the explicit condition `1 < n`:

```lean
def Counterexample (n : Nat) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ n.totient ∣ n - 1
```

For every hypothetical counterexample with exactly k distinct prime
factors, it proves `n < 2^(2^k)`. This is a corollary of the existing
Cook--Nielsen product-bound development in the original repository; it
is not a new record bound. The new bridge explicitly constructs the
increasing prime-factor enumeration and identifies its two products
with n and phi(n). No representation hypothesis is left to the caller.

It then defines the finite set

    E(k) = { n < 2^(2^k) : n > 1, n composite,
             phi(n) divides n-1, and omega(n)=k }.

The checked membership theorem is the unrestricted equivalence

    n in E(k)  <=>  n is a Lehmer counterexample and omega(n)=k.

The checked final equivalence is

    (for every n>1, phi(n) divides n-1 implies n is prime)
        <=> (for every natural k, E(k) is empty).

**Neither universal side of that equivalence has been proved here.**
In particular, the file contains no theorem asserting that E(k) is
empty for every k. The only kernel-evaluated empty-set controls are
k=0,1,2. Larger finite exclusions belong to the separately scoped
existing computational work; this supplement does not reclassify them
as Lean-verified executions of the optimized search.

## The targeted final-prime construction

Write A for the product of a proper prime prefix, B for the product of
its primes minus one, C=MB, and D=C-A>0. The exact final-entry equation is

    A*q - 1 = C*(q-1)  <=>  D*q = C-1.

The Lean file checks this equivalence and uniqueness of q when D is
nonzero. It also checks a useful exclusion for every factor count:
when D=1, q=A. If A is composite, q cannot be prime. For a one-prime
prefix this would repeat that prime and fail the distinctness/order
condition. This does not eliminate the possibilities D>1.

The exact two-entry identity is also checked:

    (D*p-C)(D*q-C) - (A*C-D)
       = D * (C*(p-1)*(q-1)-A*p*q+1).

Turning this identity into a descent would require another compatible
divisor pair that produces ordered prime entries and a smaller valid
solution. An algebraic identity does not supply such a pair. No
prime-preserving descent theorem has been obtained.

## Scope and evidence

The ten named theorem reports in `logs/UniformFinite.log` contain only
`propext`, `Classical.choice`, and/or `Quot.sound`. The compiler returned
zero. There is no `sorryAx`, native-evaluation axiom, project axiom, or
assumption of universal emptiness in these endpoints. The statements
and definitions are inspected as well as their axiom lists; a clean
axiom list alone would not detect an unproved result passed as a
theorem parameter.

The four prerequisite modules were copied byte for byte from the
original eLhmr checkout and compiled locally before the new file.
`verification-report.json` records their relationship to the immutable
v1.7.0 Git objects, the pinned Mathlib revision, compiler version,
source hashes, and final compiler output. `SHA256SUMS.txt` lists the
delivered supplement files.

The elementary finite set E(k) is intentionally impractical. It is a
different, explicitly defined enumeration from the optimized DFS in
`uniform_tree.py`. This check does not formalize every line of that
Python implementation, re-run every historical large computation, or
establish a global bound on k.

## Literature routes examined

Molnar and Singh's published *Spoof Lehmer factorizations*, Integers 26
(2026), A33, gives fixed-factor-count finiteness and computation. Its
spoof examples also show why an argument that drops primality can fail.
This supports studying prime arithmetic in addition to the product
identity; it supplies no full-conjecture proof to import.
<https://math.colgate.edu/~integers/aa33/aa33.pdf>

The 2023 elementary-symmetric-polynomial claimed solution is marked
withdrawn by its author, with an error in Theorem 2.3. It cannot be
used as a verified replacement.
<https://arxiv.org/abs/2302.07368>

The displayed final Lean types in the beautiful-numbers/lehmer-lean
README retain four explicit range-closure hypotheses. Those displayed
aggregation statements do not by themselves establish the closures.
This observation concerns the inspected exported types, not a claim
that every argument in that separate manuscript has been audited.
<https://github.com/beautiful-numbers/lehmer-lean/blob/main/README.md>

## Reproduce the new check

With the original eLhmr repository checked out at v1.7.0 and its pinned
Lean/Mathlib dependencies installed, place the supplied
`lean/UniformFinite.lean` in that checkout's `lean` directory. Then run
from that directory:

```text
lake build LehmerTotient.Product LehmerTotient.Search
lake env lean UniformFinite.lean
```

The included Python preparation and compilation scripts reproduce the
local check using the already installed Windows cache. Their absolute
cache paths are environment-specific; the Lake commands above are the
portable procedure. No PDFs, manuscript titles, publication metadata,
or existing DOI archives were altered by this supplement.

## The unresolved obligation

To claim full closure one must prove E(k) is empty for **every** k, or
prove an equivalent global contradiction. Finite tests, the bound on n
at a specified k, the forced-last-prime identity, and the deficit-one
exclusion do not establish this. The supplement therefore keeps the
full-conjecture claim explicitly unproved.
