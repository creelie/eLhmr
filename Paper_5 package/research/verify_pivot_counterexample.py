"""Exact check of a counterexample to Sautot's Lemma 6.40 as stated.

This does not produce a Lehmer counterexample or a proof of the conjecture.
Primality, products, lcms and the decisive inequalities use exact arithmetic.
Decimal logarithms in the output are illustrations, not proof inputs.
"""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import gcd, isqrt, lcm, prod
import json
from pathlib import Path


def prime_by_trial_division(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def log_enclosure(x, terms):
    """Rational bounds from log(x)=2*atanh((x-1)/(x+1)), for x>1."""
    z = Fraction(x - 1, x + 1)
    lower = 2 * sum(
        (z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)),
        Fraction(0),
    )
    tail_bound = 2 * z ** (2 * terms + 1) / (
        (2 * terms + 1) * (1 - z * z)
    )
    return lower, lower + tail_bound


def main():
    support = (7, 11, 13, 19, 31, 151, 251, 271, 751, 2251)
    removed = 13
    assert len(set(support)) == len(support)
    assert all(prime_by_trial_division(p) and p % 2 for p in support)
    assert min(support) == 7 and removed > 7

    n = prod(support)
    ell = lcm(*(p - 1 for p in support))
    ell_after = lcm(*(p - 1 for p in support if p != removed))
    phi = prod(p - 1 for p in support)
    assert n == 10237284291923908219
    assert ell == 13500 and ell_after == 6750
    assert ell // ell_after == 2
    assert gcd(n, phi) == 1

    # P(S)=log(ell)/log(n)<1/4<3/5, by monotonicity of log.
    assert n > ell**4
    # Hence P(S)*log(13)<(1/4)*log(16)=log(2).
    # The exact identity for the change of P therefore has negative numerator.
    assert removed < 2**4

    log7_lo, log7_hi = log_enclosure(7, 40)
    log2_lo, log2_hi = log_enclosure(2, 20)
    assert log7_lo > Fraction(19, 10)
    assert log7_hi < 2
    assert log2_hi < Fraction(7, 10)
    # g(t)=(2/5)t-1/(3t^3) is increasing for t>0.
    # Thus log(h(7)) > g(19/10) > 7/10 > log(2).
    t = Fraction(19, 10)
    g_lower = Fraction(2, 5) * t - Fraction(1, 3) / t**3
    assert g_lower > Fraction(7, 10)
    # Thus R=2<h(7), and delta_B(7)>1/48>0.
    assert Fraction(1, 3) / log7_hi**4 > Fraction(1, 48)

    with localcontext() as ctx:
        ctx.prec = 50
        dn, dl, dla = Decimal(n), Decimal(ell), Decimal(ell_after)
        before = dl.ln() / dn.ln()
        after = dla.ln() / Decimal(n // removed).ln()
        delta = Decimal(1) / (Decimal(3) * Decimal(7).ln()**4)
        h7 = ((Decimal(2) / 5 - delta) * Decimal(7).ln()).exp()
        report = {
            "scope": "Counterexample to the stated controlled-removal lemma; no Lehmer closure",
            "source": "https://zenodo.org/records/18911153",
            "pdf_page": 34,
            "lemma": "6.40",
            "support": list(support),
            "removed_prime": removed,
            "n": str(n),
            "L": ell,
            "L_after": ell_after,
            "R": ell // ell_after,
            "coprime_n_phi": gcd(n, phi) == 1,
            "exact_checks": {
                "all_support_entries_prime": True,
                "n_greater_than_L_fourth_power": n > ell**4,
                "13_less_than_2_fourth_power": removed < 2**4,
                "h7_greater_than_2_by_rational_log_bounds": True,
                "delta7_greater_than_one_over_48": True,
                "P_after_strictly_less_than_P_before": True,
            },
            "illustrative_decimal_values": {
                "P_before": str(before),
                "P_after": str(after),
                "gain": str(after - before),
                "delta7": str(delta),
                "h7": str(h7),
            },
        }
    target = Path(__file__).with_name("pivot-counterexample.json")
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
