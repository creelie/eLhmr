"""Check a local residue route, without asserting full conjecture closure."""
from math import prod,gcd
from pathlib import Path
import json

def main():
    # Proposed contradiction modulo the smallest possible quotient-two defect, 5.
    # These residue patterns satisfy A=2B=1 (mod 5), for arbitrarily long lists.
    for t in range(251):
        rs=[2,2,4]+[2]*(4*t)
        assert prod(rs)%5==1
        assert 2*prod(r-1 for r in rs)%5==1
        assert all(r not in (0,1) for r in rs)
    # A genuine prime prefix passes the prefix coprimality and new gcd tests.
    # Its defect is divisible by 5, not equal to 5; exact divisibility fails.
    ps=(7,17,19)
    A=prod(ps); B=prod(p-1 for p in ps); M=(A+B-1)//B; D=M*B-A
    assert M==2 and gcd(A,B)==gcd(D-1,A)==1
    assert A%5==2*B%5==1 and D%5==0 and (A-1)%D!=0
    result={'residue_pattern':'(2,2,4) followed by 4t copies of 2, modulo 5',
            'symbolic_all_t_reason':'Every block of four 2s has product 1 modulo 5; its (r-1) product is 1.',
            'finite_consistency_values_t':251,
            'genuine_prime_prefix_control':{'S':ps,'A':A,'B':B,'M':M,'D':D,
                'gcd_D_minus_1_A':gcd(D-1,A),'D_divides_A_minus_1':False},
            'limitation':'Residue patterns are not exact-defect constructions. No prime tuple satisfying every required equality is produced.',
            'full_conjecture_proved':False}
    out=Path(__file__).resolve().parent/'verification/residue-route.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))

if __name__=='__main__': main()
