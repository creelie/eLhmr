"""Symbolic checks of displayed identities; not a proof of prime-tail exclusion."""
from pathlib import Path
import json


class Polynomial:
    """Sparse polynomials over Z in the seven displayed indeterminates."""

    def __init__(self, terms=0):
        if isinstance(terms, int):
            terms = {} if terms == 0 else {(0,) * 7: terms}
        self.terms = {e: c for e, c in terms.items() if c}

    def __add__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        result = dict(self.terms)
        for e, c in other.terms.items():
            result[e] = result.get(e, 0) + c
        return Polynomial(result)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        return self + (-other)

    def __rsub__(self, other):
        return Polynomial(other) + (-self)

    def __mul__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        result = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                g = tuple(a + b for a, b in zip(e, f))
                result[g] = result.get(g, 0) + c * d
        return Polynomial(result)

    __rmul__ = __mul__

    def __pow__(self, power):
        assert isinstance(power, int) and power >= 0
        result = Polynomial(1)
        for _ in range(power):
            result = result * self
        return result

    def is_zero(self):
        return not self.terms


def variable(index):
    exponents = [0] * 7
    exponents[index] = 1
    return Polynomial({tuple(exponents): 1})


A, B, M, p, q, C, u = [variable(i) for i in range(7)]
D = M * B - A
one_target = A * q - 1 - M * B * (q - 1)
two_target = A * p * q - 1 - M * B * (p - 1) * (q - 1)
K = M * A * B - D
checks = {
    'one_tail_identity': (D * q - (M * B - 1) + one_target).is_zero(),
    'two_tail_factorisation': (
        (D * p - M * B) * (D * q - M * B) - K + D * two_target).is_zero(),
    'K_rewriting': (K - (A**2 + D * (A - 1))).is_zero(),
    'intermediate_tail_identity': (
        (D * p - M * B) * (q - 1) - A * p + 1 + two_target).is_zero(),
    # Denominators are cleared: multiply the rational identity by D^2*u.
    'recovered_product_formula': (
        (u + M * B) * (K + M * B * u)
        - (K * u + M * B * (u**2 + K) + (M * B)**2 * u)).is_zero(),
    # Multiply the recovery identity by C; C>0 in the manuscript.
    'extreme_divisor_recovers_composite_multiple': (
        A**2 + C * (A - 1) + A + C - A * (C + A + 1)).is_zero(),
    'explicit_integer_control': 15 * 17 * 255 - 1 == 2 * 8 * 16 * 254 == 65024,
    'explicit_composite_tail': 255 == 3 * 5 * 17,
}
assert all(checks.values()), checks
report = {'status': 'passed', 'checks': checks,
          'scope': 'Exact symbolic identities and integer control only; no universal exclusion',
          'full_Lehmer_conjecture_proved': False,
          'engine': 'Integer-coefficient sparse polynomial normalisation; Python standard library'}
Path(__file__).with_name('exact-algebra-checks.json').write_text(
    json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(report, indent=2))
