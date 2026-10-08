"""Section 9.9 of the paper: what a prime factor l of the last defect forces.

Let n = A q be a composite solution of n - 1 = 2 phi(n) with largest prime factor q, let S be the other prime factors,
A = prod S, B = phi(A) and C = 2B - A (the last defect).  If a prime l divides C, then l is not in S, no element of S
is 1 modulo l, and prod_S p/(p-1) < 2 < prod_S p/(p-1) * q/(q-1) (Lemma 9.12).  An *l-set* of size K is an
independent set S of K primes >= 5, none equal to l or 1 modulo l, with prod_S p/(p-1) < 2 < prod_S p/(p-1) * q0/(q0-1),
where q0 is the least prime above max S that is not 1 modulo an element of S.  k_l is the least K + 1 for which an
l-set exists (Proposition 9.13); for every l-set, A q is a solution with l | C exactly when l | C,
C | A - 1 and q = (2B - 1)/C is a prime above max S, not 1 modulo an element of S (Proposition 9.14).

The search is that of Proposition 2.5 with l and the primes 1 mod l removed from S: depth first; at a set with r
elements still to choose the children are its candidates t in increasing order, the loop stops at the first t whose
bound (t, the r - 1 candidates of the parent after t, and the least allowed q above them) is at most 2, and a child
is skipped when the bound with its own candidates is at most 2 or when its product is at least 2.  Bounds in double
precision with a margin (default 1e-9) on the logarithm, so rounding can add sets but never remove one; every set of
the full size is decided in exact rational arithmetic.  An error is raised instead of truncating when the table of
primes (up to 3e7) is too short.

usage: python3 defect/defect_bound.py l [Kmax] [margin]        least k for l (scanning K = 2, 3, ...)
       (defect/defect_scan.py runs this over a range of l, defect/defect_leaves.py lists every l-set)"""
import sys, math
from fractions import Fraction
from sympy import primerange, isprime

LIMIT = 30_000_000
PR = list(primerange(5, LIMIT))
LG = [math.log(p / (p - 1)) for p in PR]
LOG2 = math.log(2)


def cands(S, l, start, need, restricted, strict=True):
    """table indices of the first `need` primes after index `start` that are not 1 modulo an element of S and,
    if restricted, are neither l nor 1 modulo l.  At the end of the table: an error, or (strict=False) fewer."""
    out = []
    i = start
    while len(out) < need:
        i += 1
        if i >= len(PR):
            if strict:
                raise RuntimeError("table of primes too short")
            return out
        p = PR[i]
        if any(p % s == 1 for s in S):
            continue
        if restricted and (p == l or p % l == 1):
            continue
        out.append(i)
    return out


def product(ps):
    P = Fraction(1)
    for p in ps:
        P *= Fraction(p, p - 1)
    return P


def decide(S, l):
    """the equation for the l-set S: returns (l | C, C | A - 1, solution or None)."""
    A = 1
    B = 1
    for p in S:
        A *= p
        B *= p - 1
    C = 2 * B - A
    if C % l:
        return False, False, None
    if (A - 1) % C:
        return True, False, None
    q = (2 * B - 1) // C
    if q > S[-1] and all(q % s != 1 for s in S) and isprime(q):
        return True, True, list(S) + [q]
    return True, True, None


def search(l, K, margin=1e-9, all_sets=False, cap=None):
    """l-sets of size K for l.  Returns (first l-set or None, statistics); with all_sets=True
    every l-set is listed and decided (stops after `cap` sets if cap is given)."""
    st = dict(nodes=0, sets=0, div_l=0, div_A=0, solutions=[], capped=False)
    first = None
    stack = [((), -1, 0.0)]
    while stack:
        S, pos, lp = stack.pop()
        st['nodes'] += 1
        r = K - len(S)
        if r == 0:
            qi = cands(S, l, pos, 1, False)[0]
            if lp + LG[qi] > LOG2 - margin:
                P = product(S)
                if P < 2 and P * Fraction(PR[qi], PR[qi] - 1) > 2:
                    st['sets'] += 1
                    if first is None:
                        first = list(S) + [PR[qi]]
                    if not all_sets:
                        return first, st
                    dl, dA, sol = decide(S, l)
                    st['div_l'] += dl
                    st['div_A'] += dA
                    if sol:
                        st['solutions'].append(sol)
                    if cap and st['sets'] >= cap:
                        st['capped'] = True
                        return first, st
            continue
        w = 400 + 4 * r
        while True:
            cs = cands(S, l, pos, w, True, strict=False)
            kids = []
            stopped = False
            for a, t in enumerate(cs):
                rest = cs[a + 1:a + r]
                if len(rest) < r - 1:
                    break
                # bound with the parent's candidates: ignores t's own condition, so it decreases with t
                wq = cands(S, l, rest[-1] if rest else t, 1, False)[0]
                if lp + LG[t] + sum(LG[x] for x in rest) + LG[wq] <= LOG2 - margin:
                    stopped = True
                    break
                S2 = S + (PR[t],)
                rest2 = cands(S2, l, t, r - 1, True) if r > 1 else []
                q = cands(S2, l, rest2[-1] if rest2 else t, 1, False)[0]
                if lp + LG[t] + sum(LG[x] for x in rest2) + LG[q] <= LOG2 - margin:
                    continue
                if lp + LG[t] >= LOG2 + margin:
                    continue                      # product at least 2; near-ties go on to the exact test
                kids.append((S2, t, lp + LG[t]))
            if stopped:
                break
            if len(cs) < w:
                raise RuntimeError("table of primes too short")
            w *= 4                                # window too short: widen it and redo this set
        stack.extend(reversed(kids))
    return first, st


def least_k(l, Kmax, margin=1e-9, Kmin=2):
    for K in range(Kmin, Kmax + 1):
        w, st = search(l, K, margin)
        if w:
            return K + 1, w
    return None, None


if __name__ == "__main__":
    l = int(sys.argv[1])
    Kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    margin = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-9
    for K in range(2, Kmax + 1):
        w, st = search(l, K, margin)
        print(f"l = {l}: k = {K + 1}: {'possible, e.g. ' + str(w) if w else 'impossible'} ({st['nodes']} nodes)",
              flush=True)
        if w:
            break
