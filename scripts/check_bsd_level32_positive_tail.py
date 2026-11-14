#!/usr/bin/env python3
"""Exact rational certificate for the level-32 CM eta positive-tail cut.

NOT a proof that the E:y²=x³-x L-function equals the eta Mellin integral;
NOT an Agda-kernel acceptance. The proof of the analytic inequalities
is in docs/bsd-level32-positive-tail-proof-20261114.md.

For t >= t0=1/sqrt(32), q=exp(-8*pi*t) <= 1/16 from
pi>3, sqrt(2)>4/3 and exp(4)>16. For all N,
  P_N(t)=prod_{n=1}^N (1-q^n)^2(1-q^(2n))^2 >= 73/85.
For M>N, 0 <= P_N(t)-P_M(t) <= delta_N where
  delta_N = 2(1/16)^(N+1)/(1-1/16)
            + 2(1/16)^(2*N+2)/(1-(1/16)^2).

This executable certificate checks exact rational constants and finite
regressions, not a real-analysis proof or same-object identifications.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction

QMAX = Fraction(1, 16)
LOWER_BOUND = Fraction(73, 85)


def global_defect(q: Fraction) -> Fraction:
    """Exact geometric sum."""
    if not 0 <= q < 1:
        raise ValueError("geometric ratio must be in [0,1)")
    return 2 * q / (1 - q) + 2 * q**2 / (1 - q**2)


def tail_defect(n: int, q: Fraction = QMAX) -> Fraction:
    if n < 0 or not 0 <= q < 1:
        raise ValueError("need n>=0 and 0<=q<1")
    return 2 * q ** (n + 1) / (1 - q) + 2 * q ** (2 * (n + 1)) / (1 - q**2)


def finite_eta_product(n: int, q: Fraction) -> Fraction:
    """Exact finite-product regression, not a proof of every finite N."""
    if n < 0 or not 0 <= q < 1:
        raise ValueError("need n>=0 and 0<=q<1")
    product = Fraction(1)
    for k in range(1, n + 1):
        product *= (1 - q**k)**2 * (1 - q**(2 * k))**2
    return product


def certify(n: int = 10) -> dict:
    if not 0 <= n <= 24:
        raise ValueError("finite regression cutoff must be between 0 and 24")
    assert global_defect(QMAX) == Fraction(12, 85)
    assert 1 - global_defect(QMAX) == LOWER_BOUND
    assert tail_defect(0) == global_defect(QMAX)
    for i in range(n + 1):
        assert tail_defect(i + 1) < tail_defect(i)
        for q in (Fraction(0), Fraction(1, 64), Fraction(1, 32), QMAX):
            p_i = finite_eta_product(i, q)
            assert LOWER_BOUND <= p_i <= 1
            assert p_i - finite_eta_product(i + 1, q) <= tail_defect(i, QMAX)
        assert finite_eta_product(i, QMAX) - finite_eta_product(n + 1, QMAX) <= tail_defect(i)
    return {
        "curve": "E: y^2=x^3-x, conductor 32",
        "uniform_t_range": "t >= 1/sqrt(32)",
        "upper_bound_for_exp_minus_8pi_t": str(QMAX),
        "geometric_error_sum": str(global_defect(QMAX)),
        "uniform_infinite_eta_product_lower_bound": str(LOWER_BOUND),
        "tail_defect_after_n": n,
        "tail_defect_bound": str(tail_defect(n)),
        "conditional_L_E_1_lower_bound": "(146/85)*exp(-2*pi/sqrt(32))",
        "finite_fraction_regressions": True,
        "symbolic_induction_documented": True,
        "same_object_modularity_proved": False,
        "bishop_exponential_and_eta_constructed": False,
        "mellin_identification_proved": False,
        "agda_kernel_accepted": False,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--n", type=int, default=10)
    args = p.parse_args()
    print(json.dumps(certify(args.n), indent=2))


if __name__ == "__main__":
    main()
