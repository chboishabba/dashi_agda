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
    # BOTH horizontal sides of Re(s)=1/2, on the SAME original
    # signed-quartic source. Reflection alpha -> -alpha does not
    # reverse Q: the even defect doubles; only linear displacement cancels.
    # This is not a zero-free theorem on the actual zeta function.
    mirror_cases = 0
    for den in (2,3,11,1000,1000000):
        alpha=Q(1,den)
        beta_right=Q(1,2)+alpha
        beta_left=Q(1,2)-alpha
        assert beta_right+beta_left==1
        assert (beta_right-Q(1,2))+(beta_left-Q(1,2))==0
        assert (beta_right-Q(1,2))**2+(beta_left-Q(1,2))**2==2*alpha**2
        for ordinate in (Q(0), alpha, Q(2)*alpha, Q(12,5)*alpha):
            assert quartic(alpha,ordinate)==quartic(-alpha,ordinate)
            assert is_cone(alpha,ordinate)==is_cone(-alpha,ordinate)
            assert quartic(alpha,ordinate)+quartic(-alpha,ordinate)==2*quartic(alpha,ordinate)
            mirror_cases+=1

    # The separate external source's conservatively rounded one-sided
    # target cap has an exact reflected left endpoint. Importing its
    # same-zeta nonvanishing theorem remains an INDEPENDENT obligation.
    safe_beta=Q(437479,500000)
    safe_left=1-safe_beta
    safe_displacement=safe_beta-Q(1,2)
    assert safe_left==Q(62521,500000)
    assert safe_displacement==Q(187479,500000)
    assert safe_beta-Q(1,2)==Q(1,2)-safe_left
    assert Q(0)<safe_left<Q(1,2)<safe_beta<1

    # Exact counterexample to the *invalid* inference
    # "reflection symmetry alone implies every zero is on the line".
    # This rational polynomial is NOT a zeta/completed L-function.
    # f(s)=(s-1/4)(s-3/4)=f(1-s), but its two roots are off-line.
    def toy_symmetric_function(s):
        return (s-Q(1,4))*(s-Q(3,4))
    for sample in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):
        assert toy_symmetric_function(sample)==toy_symmetric_function(1-sample)
    assert toy_symmetric_function(Q(1,4))==toy_symmetric_function(Q(3,4))==0
    assert Q(1,4)!=Q(1,2) and Q(3,4)!=Q(1,2)

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
        "horizontal_reflection_cases":mirror_cases,
        "horizontal_signed_displacement_cancels":True,
        "horizontal_even_defect_doubles":True,
        "reflected_safe_left_beta":str(safe_left),
        "reflected_safe_horizontal_radius":str(safe_displacement),
        "reflection_symmetry_alone_implies_RH":False,
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
