"""Exact test of the proposed repeated-(p-1)-factor obstruction.

The written note proves the identities for all prefixes. These finite tests
are consistency checks and do not prove the Lehmer conjecture.
"""
from pathlib import Path
from itertools import combinations
from math import prod,gcd
import json
from single_candidate import prime,candidate

def strip_supported_part(a,N):
    assert a>0 and N>0
    rough=a
    while (g:=gcd(rough,N))>1:
        rough//=g
    return a//rough,rough

def v(n,p):
    assert n>0
    z=0
    while n%p==0:
        n//=p
        z+=1
    return z

def inspect(S):
    c=candidate(S,-1)
    N=c.M*c.B
    if gcd(c.D,N)!=1:
        return None
    U,V=strip_supported_part(c.A-1,N)
    original=(c.A-1)%c.D==0
    stripped=V%c.D==0
    assert original==stripped
    out={'prefix':S,'M':c.M,'D':c.D,'smooth_part':U,'rough_part':V,
         'divisibility':original}
    if original:
        q=1+(c.A-1)//c.D
        assert c.A*q-1==N*(q-1)
        assert gcd(q,c.A)==gcd(c.D-1,c.A)
        for ell in (2,3,5,7,11,13,17,19,23,29,31):
            if N%ell==0:
                assert v(c.A-1,ell)==v(q-1,ell)
                assert v(c.A*q-1,ell)==v(N,ell)+v(q-1,ell)
        out.update(q=q,tail_coprime_to_prefix=gcd(q,c.A)==1)
    return out

def main():
    ps=[p for p in range(3,48,2) if prime(p)]
    checked=eligible=completions=0
    for k in range(1,7):
        for S in combinations(ps,k):
            checked+=1
            out=inspect(S)
            if out is not None:
                eligible+=1
                completions+=int(out['divisibility'])
    # A supplied spoof example: genuine prime prefix, composite largest entry.
    S=(3,5,17,257,65717)
    assert all(prime(p) for p in S)
    control=inspect(S)
    assert control['D']==181 and control['q']==23794275
    assert control['q']>max(S) and not prime(control['q'])
    result={'prefixes_checked':checked,'coprime_defects_checked':eligible,
            'integer_completions_in_bounded_test':completions,
            'stripped_test_equivalent_in_all_cases':True,
            'valuation_identities':'all tested eligible completions passed',
            'prime_prefix_composite_tail_control':control,
            'conclusion':'The proposed valuation filter is algebraically redundant after exact candidate divisibility. It supplies no all-length exclusion.',
            'full_conjecture_proved':False}
    root=Path(__file__).resolve().parent
    (root/'verification/valuation-route.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':
    main()
