import os
# Generates lean/LehmerTotient/Data.lean: lists of primes and composite witnesses for the
# threshold lemmas.
from sympy import isprime, primerange
def spf(x):
    for w in range(2, x):
        if x % w == 0: return w
def lists(start, step, last):
    L=[]; W=[]
    x=start
    while x<=last:
        if isprime(x): L.append(x)
        else: W.append(spf(x))
        x+=step
    return L,W
def fmt(name, xs, doc):
    lines=[]; cur=[]
    for v in xs:
        cur.append(str(v))
        if sum(len(c)+2 for c in cur)>88:
            lines.append(", ".join(cur)); cur=[]
    if cur: lines.append(", ".join(cur))
    body=",\n  ".join(lines)
    return f"/-- {doc} -/\ndef {name} : List Nat := [\n  {body}]\n"
out=["/-!\n# Data for the threshold lemmas\n\nGenerated lists: primes in an arithmetic progression and, for each composite member of the\nprogression below the last prime, its least prime factor.\n-/\n\nnamespace LehmerTotient\n"]
qs=[p for p in primerange(5,40000) if p%3==2][:1538]
L,W=lists(5,6,qs[-1]); assert L==qs
out.append(fmt("primesMod6", L, "The first 1538 primes congruent to `5` modulo `6`."))
out.append(fmt("witnessesMod6", W, "Least prime factors of the composite `x ≡ 5 (mod 6)` with `5 ≤ x ≤ 27941`."))
print(len(L), len(W), (qs[-1]-5)//6+1)
L2,W2=lists(5,2,139); assert len(L2)==32, len(L2)
out.append(fmt("primesFrom5", L2, "The 32 primes from `5` to `139`."))
out.append(fmt("witnessesFrom5", W2, "Least prime factors of the odd composites between `5` and `139`."))
L3,W3=lists(3,2,19); assert len(L3)==7
out.append(fmt("oddPrimes7", L3, "The seven odd primes from `3` to `19`."))
out.append(fmt("witnessesOdd7", W3, "Least prime factors of the odd composites between `3` and `19`."))
print(len(L2),len(W2),len(L3),W3)
out.append("end LehmerTotient\n")
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'LehmerTotient', 'Data.lean'),'w').write("\n".join(out))
