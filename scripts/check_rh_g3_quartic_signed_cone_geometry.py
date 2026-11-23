#!/usr/bin/env python3
"""RH G3 quartic signed cone: exact rational sign geometry and negative controls.

The repo's genuine signed-pole frontiers already contain a normalized
fourth-order source:
    Q(alpha,q) = alpha^2*q^2 - (alpha^4+q^4)/6.
This checker does NOT prove zeta-zero admissibility or an eventual
strict signed compensation inequality. It tests a sharp finite,
rational algebraic obstruction to replacing signed cone mass with an
unconditional positive/negative absolute estimate.

If alpha != 0 and r=(q/alpha)^2 then
    6 Q/alpha^4 = 6r - 1 - r^2.
For r=0 and r=1 INSIDE cone q^2<=6*alpha^2, the signs are opposite.
Both cases can occur with alpha rational of arbitrarily small size.
All samples use Fraction; no numerical epsilon, float or zeta-zero claim.
"""
from __future__ import annotations

import json
from fractions import Fraction as Q


def quartic(alpha: Q, ordinate: Q) -> Q:
    return alpha*alpha*ordinate*ordinate - (
        alpha**4+ordinate**4)/6


def is_cone(alpha: Q, ordinate: Q) -> bool:
    return ordinate*ordinate <= 6*alpha*alpha


def status(v: Q) -> str:
    return "positive" if v>0 else ("negative" if v<0 else "zero")


def main() -> None:
    cases=[]
    for denominator in (1, 2, 3, 11, 1000, 1000000):
        alpha=Q(1,denominator)
        for ratio in (Q(0), Q(1), Q(2), Q(12,5), Q(2449,1000)):
            ordinate=ratio*alpha
            r=ratio**2
            q4=quartic(alpha,ordinate)
            assert (6*q4)/(alpha**4) == 6*r-1-r*r
            assert is_cone(alpha,ordinate)
            if ratio == 0:
                assert q4 == -alpha**4/6
            if ratio == 1:
                assert q4 == Q(2,3)*alpha**4
            cases.append({
                "alpha":str(alpha),"q_over_alpha":str(ratio),
                "quartic_sign":status(q4),
                "normalized_sixQ_over_alpha4":str(6*q4/alpha**4)})
    assert status(quartic(Q(1),Q(0)))=="negative"
    assert status(quartic(Q(1),Q(1)))=="positive"
    assert status(quartic(Q(1),Q(2449,1000)))=="negative"

    # The maximum of the quartic at fixed alpha is at r=3.
    # It is irrelevant as a uniform negative contribution: there is a
    # definite positive portion inside the canonical mixed cone.
    r=Q(3)
    assert 6*r-1-r*r==8

    print(json.dumps({
        "schema":"rh_g3_quartic_signed_cone_geometry_exact_v1",
        "source":"RiemannQuarticSignedPoleCompensationExact + ConeDebtExact",
        "exact_fraction_cases":len(cases),
        "inside_mixed_cone_has_both_signs":True,
        "same_ordinate_quartic_negative":True,
        "q_equals_alpha_quartic_positive":True,
        "near_boundary_cone_negative":True,
        "quartic_profile":"alpha^4*(6r-1-r^2)/6; r=(q/alpha)^2",
        "samples":cases[:10],
        "actual_zeros_or_rho_admissible_configurations_constructed":False,
        "uniform_signed_compensation_gap_proved":False,
        "strict_RH_G3_or_RH_derived":False,
        "agda_lean_kernel_accepted_here":False
    },indent=2))


if __name__=="__main__":
    main()
