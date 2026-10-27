"""Positive and negative controls for the all-k construction; not an all-k exclusion."""
from pathlib import Path
from itertools import combinations
from math import prod
import json
from uniform_tree import construct, Limits, prime, next_bound

ROOT = Path(__file__).parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
results = []
known = {2: [15], 3: [255], 4: [65535],
         5: [83623935, 4294967295], 6: [6992962672132095]}
for sign, counts in ((-1, range(2, 12)), (1, range(2, 7))):
    for k in counts:
        result = construct(k, sign, Limits(nodes=500000, prime_upper=300000, trial_divisor=1000000))
        if result['complete_for_this_k']:
            ns = [h['n'] for h in result['solutions']]
            assert ns == ([] if sign == -1 else known[k]), (k, sign, ns)
        results.append(result)
        print(json.dumps({'k': k, 'sign': sign, 'complete': result['complete_for_this_k'],
                          'nodes': result['statistics']['nodes'], 'solutions': len(result['solutions'])}), flush=True)
        if not result['complete_for_this_k']:
            break

# An independent product-equation check over ALL tuples from a small prime set.
ps = [p for p in range(3, 32, 2) if prime(p)]
compared = 0
for k in range(2, 6):
    for sign in (-1, 1):
        result = next(r for r in results if r['k'] == k and r['sign'] == sign)
        assert result['complete_for_this_k']
        actual = {tuple(h['factors']) for h in result['solutions'] if max(h['factors']) <= 31}
        expected = set()
        for factors in combinations(ps, k):
            n, phi = prod(factors), prod(p - 1 for p in factors)
            if (n + sign) % phi == 0:
                expected.add(factors)
            compared += 1
        assert actual == expected

# Exercise the failure mode: a budgeted partial traversal must not be certified empty.
stopped = construct(6, 1, Limits(nodes=1, prime_upper=300000, trial_divisor=1000000))
assert not stopped['complete_for_this_k'] and stopped['stop_reason'] == 'Node budget reached'

# Check both cutoff inequalities against every proper prefix of positive controls.
cutoff_checks = 0
for r in results:
    for hit in r['solutions']:
        fs, M = hit['factors'], hit['M']
        for j in range(len(fs) - 1):
            A, B = prod(fs[:j]), prod(p - 1 for p in fs[:j])
            assert fs[j] <= next_bound(A, B, M, len(fs) - j, r['sign'])
            cutoff_checks += 1

report = {'status': 'PASS', 'runs': results,
          'independent_small_tuple_comparisons': compared,
          'known_companion_solutions_reproduced': sum(len(r['solutions']) for r in results if r['sign'] == 1),
          'known_solution_prefix_cutoffs_checked': cutoff_checks,
          'resource_stop_negative_control': 'PASS',
          'all_k_exclusion_proved': False,
          'uniform_construction_proof': 'Written theorem; not inferred from tests.'}
(OUT / 'uniform-tree-controls.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k != 'runs'}, indent=2))
