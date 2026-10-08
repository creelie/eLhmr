import sys, collections, json
sval = sys.argv[1]
sys.argv = ['x', sval]
src = open('search.py').read()
src = src.replace('    stats["nodes"] += 1\n', '    stats["nodes"] += 1\n    H[j] += 1\n    MS[need] += 1\n')
src = src.replace('                stats["lasttests"] += 1\n', '                stats["lasttests"] += 1\n                LT[j] += 1\n')
H = collections.Counter(); LT = collections.Counter(); MS = collections.Counter()
exec(compile(src, 'search', 'exec'))
out = {"s": int(sval), "nodes": stats["nodes"], "maxdepth": stats["maxdepth"], "lasttests": stats["lasttests"],
       "by_depth": sorted(H.items()), "lasttests_by_depth": sorted(LT.items()), "need": sorted(MS.items())}
print(json.dumps(out))
open('hist_s%s.json' % sval, 'w').write(json.dumps(out))
