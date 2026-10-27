"""A complete finite construction for EACH prescribed factor count.

This is not a proof that the minus-sign output is empty for EVERY count.
The unbounded algorithm terminates for each finite k by the written theorem.
Optional resource limits return complete=False, never a false empty certificate.
All primality decisions use trial division. Run Python without -O.
"""
from dataclasses import dataclass, asdict
from math import gcd, isqrt, prod
from pathlib import Path
import argparse, json


class Incomplete(Exception):
    pass


@dataclass
class Limits:
    nodes: int | None = 200000
    prime_upper: int | None = 1000000
    trial_divisor: int | None = 1000000


def prime(n, trial_cap=None):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    root = isqrt(n)
    end = root if trial_cap is None else min(root, trial_cap)
    for d in range(3, end + 1, 2):
        if n % d == 0:
            return False
    if trial_cap is not None and root > trial_cap:
        raise Incomplete('Primality trial-division budget reached')
    return True


def next_bound(A, B, M, t, sign):
    D = M * B - A
    assert D > 0 and t >= 1
    linear = 1 + (t * A + (1 if sign == 1 else -1)) // D
    if sign == 1:
        return linear
    # Strict odd-spacing bound: D(MB+A)(p-2) < 2tA^2.
    odd = 2 + (2 * t * A * A - 1) // (D * (M * B + A))
    return min(linear, odd)


def construct(k, sign=-1, limits=None):
    if not __debug__:
        raise RuntimeError('Run the exact checker without -O.')
    if k < 2 or sign not in (-1, 1):
        raise ValueError('Use k>=2 for composite odd squarefree numbers, sign -1 or +1.')
    lim = limits if limits is not None else Limits(None, None, None)
    max_M = min(isqrt(2 * k), (k + 1) // 2) if sign == -1 else (k + 3) // 2
    stats = {'nodes': 0, 'prime_choices': 0, 'integer_tail_candidates': 0,
             'tail_primality_tests': 0, 'maximum_next_prime_bound': 0}
    hits = []

    def expand(ps, A, B, M, t):
        stats['nodes'] += 1
        if lim.nodes is not None and stats['nodes'] > lim.nodes:
            raise Incomplete('Node budget reached')
        D = M * B - A
        assert D > 0 and gcd(A, M * B) == 1
        r = ps[-1] if ps else 1
        if t == 1:
            q, rem = divmod(M * B + sign, D)
            if rem or q <= r:
                return
            stats['integer_tail_candidates'] += 1
            if gcd(A * q, M * B * (q - 1)) != 1:
                return
            stats['tail_primality_tests'] += 1
            if prime(q, lim.trial_divisor):
                factors = ps + (q,)
                n, phi = A * q, B * (q - 1)
                assert n + sign == M * phi
                assert len(set(factors)) == len(factors) == k
                hits.append({'factors': list(factors), 'n': n, 'phi': phi, 'M': M})
            return
        upper = next_bound(A, B, M, t, sign)
        stats['maximum_next_prime_bound'] = max(stats['maximum_next_prime_bound'], upper)
        lower = max(r + 2, M * B // D + 1)
        if lower % 2 == 0:
            lower += 1
        if upper < lower:
            return
        if lim.prime_upper is not None and upper > lim.prime_upper:
            raise Incomplete('Next-prime interval budget reached')
        for p in range(lower, upper + 1, 2):
            if gcd(A, p - 1) != 1 or M % p == 0:
                continue
            if p == 3 and M % 3 != (-sign) % 3:
                continue
            if not prime(p, lim.trial_divisor):
                continue
            stats['prime_choices'] += 1
            AA, BB = A * p, B * (p - 1)
            assert M * BB - AA > 0 and gcd(AA, M * BB) == 1
            yield ps + (p,), AA, BB, M, t - 1

    complete, reason = True, None
    try:
        # Explicit DFS frames avoid a fixed Python recursion-depth cutoff on k.
        frames = [iter(((), 1, 1, M, k) for M in range(2, max_M + 1))]
        while frames:
            try:
                node = next(frames[-1])
            except StopIteration:
                frames.pop()
                continue
            frames.append(expand(*node))
    except Incomplete as err:
        complete, reason = False, str(err)
    hits.sort(key=lambda h: h['n'])
    return {'k': k, 'sign': sign, 'complete_for_this_k': complete,
            'stop_reason': reason, 'M_upper_bound': max_M, 'limits': asdict(lim),
            'statistics': stats, 'solutions': hits,
            'scope': 'Only this specified k. No inference that all k have been checked.',
            'full_lehmer_conjecture_proved': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('k', type=int)
    p.add_argument('--sign', type=int, choices=(-1, 1), default=-1)
    p.add_argument('--unbounded', action='store_true', help='Remove computational budgets; may take an impractical time.')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    r = construct(a.k, a.sign, None if a.unbounded else Limits())
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(r, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(r, indent=2))


if __name__ == '__main__':
    main()
