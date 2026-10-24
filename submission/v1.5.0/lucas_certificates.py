"""Generate or independently verify complete Lucas primality certificates.

Verification uses Python's standard library only. FLINT is used only to
discover factorizations when generating certificates; no FLINT result is
trusted by the verifier. Run with --verify CERT.json for portable checking.
"""
from pathlib import Path
from math import gcd,prod
import json,sys,time

def verify_certificate(data):
    if not __debug__:
        raise RuntimeError('Do not run the certificate verifier with Python optimization enabled.')
    nodes=data['nodes']
    done=set()
    active=set()
    def check(n):
        if n in done:
            return
        assert isinstance(n,int) and n>=2
        assert n not in active
        active.add(n)
        node=nodes[str(n)]
        if n==2:
            assert node=={'base_prime':2}
        else:
            factors=node['factorization_of_n_minus_1']
            assert factors and [q for q,e in factors]==sorted(set(q for q,e in factors))
            assert all(isinstance(q,int) and isinstance(e,int) and 2<=q<n and e>=1 for q,e in factors)
            assert prod(q**e for q,e in factors)==n-1
            for q,e in factors:
                check(q)
            a=node['witness']
            assert isinstance(a,int) and 1<a<n
            assert pow(a,n-1,n)==1
            assert all(gcd(pow(a,(n-1)//q,n)-1,n)==1 for q,e in factors)
        active.remove(n)
        done.add(n)
    for n in data['roots']:
        check(n)
    assert set(nodes)==set(str(n) for n in done)
    return {'roots_proved_prime':len(data['roots']),'prime_nodes':len(done),
            'maximum_root_digits':max(len(str(n)) for n in data['roots']),
            'verification':'PASS, standard-library integer arithmetic only'}

def verify_stored_data(data, raw):
    expected=sorted(set(int(q) for row in raw['hard_leaves'] for q in row['D_factorization']))
    assert data['roots']==expected
    for row in raw['hard_leaves']:
        A=prod(row['chain'])
        B=prod(p-1 for p in row['chain'])
        C=2*B-A
        D=2*A*B-C
        assert (C,D)==(row['C'],row['D'])
        assert prod(int(q)**int(e) for q,e in row['D_factorization'].items())==D
    result=verify_certificate(data)
    result['stored_factorizations_checked']=len(raw['hard_leaves'])
    return result

def generate(roots):
    import flint
    nodes={}
    started=time.time()
    def prove(n):
        if str(n) in nodes:
            return
        if n==2:
            nodes['2']={'base_prime':2}
            return
        fs=sorted((int(q),int(e)) for q,e in flint.fmpz(n-1).factor())
        assert prod(q**e for q,e in fs)==n-1
        for q,e in fs:
            prove(q)
        for a in range(2,min(n,10000)):
            if pow(a,n-1,n)==1 and all(gcd(pow(a,(n-1)//q,n)-1,n)==1 for q,e in fs):
                nodes[str(n)]={'factorization_of_n_minus_1':fs,'witness':a}
                return
        raise RuntimeError(f'No small Lucas witness found for {n}')
    for j,n in enumerate(roots):
        prove(n)
        print(json.dumps({'root':j+1,'of':len(roots),'digits':len(str(n)),
                          'nodes':len(nodes),'seconds':round(time.time()-started,2)}),flush=True)
    return {'method':'complete Lucas primality criterion','roots':roots,'nodes':nodes}

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--verify':
        path=Path(sys.argv[2])
        data=json.loads(path.read_text())
        source=path.parent/'k14-stored-data.json'
        if len(sys.argv)>4 and sys.argv[3]=='--data':
            source=Path(sys.argv[4])
        raw=json.loads(source.read_text())
        print(json.dumps(verify_stored_data(data,raw)))
    else:
        root=Path(__file__).resolve().parent
        raw=json.loads((root/'repository/data/k14_data.json').read_text())
        roots=sorted(set(int(q) for row in raw['hard_leaves'] for q in row['D_factorization']))
        data=generate(roots)
        result=verify_stored_data(data,raw)
        out=root/'verification/k14-lucas-certificates.json'
        out.write_text(json.dumps(data,indent=2)+'\n')
        (root/'verification/k14-stored-data.json').write_text(json.dumps(raw,indent=2)+'\n')
        (root/'verification/k14-lucas-summary.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result),flush=True)
