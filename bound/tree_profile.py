import sys, collections, json, math
sval = sys.argv[1]
sys.argv = ['x', sval]
src = open('search.py').read()
hook = '''    stats["nodes"] += 1
    _lp = math.log2(max(P.bit_length() - 1 + math.log2(P / (1 << (P.bit_length() - 1))), 1e-9)) if P > 1 else None
    _V = need * F * (P + 1) / (need * F - P)
    _lv = math.log2(math.log2(_V))
    REC[j].append((_lp, _lv, float(ratio)))
'''
src = src.replace('    stats["nodes"] += 1\n', hook)
src = 'import math\n' + src
REC = collections.defaultdict(list)
exec(compile(src, 'search', 'exec'))
out = {}
for j, L in sorted(REC.items()):
    lp = [x[0] for x in L if x[0] is not None]
    lv = [x[1] for x in L]
    rr = [x[2] for x in L]
    out[j] = {"n": len(L), "lp": [min(lp), max(lp)] if lp else None, "lv": [min(lv), max(lv)], "r": [min(rr), max(rr)]}
print(json.dumps(out, indent=0))
open('prof_s%s.json' % sval, 'w').write(json.dumps(out))
