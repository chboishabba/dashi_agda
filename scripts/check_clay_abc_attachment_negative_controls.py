#!/usr/bin/env python3
"""Fail-closed arithmetic countermodels for imported Clay A/B/C attachments.

These refute specific *proposed inequalities or logical inferences*, never
refute RH, NS, YM, P != NP, Hodge, or BSD themselves. All exact claims use
Python Fraction/integer arithmetic. Logarithmic threshold uses an ordinary
floating sanity check and no proof/Agda authority.

Source provenance: Docs/roadmaps/ClaySixFrontierABCMaximumCut20261114.md
14 November 2026; BSD selected original y^2=x^3-x (LMFDB 32a2).
"""
from fractions import Fraction
from math import log, pi

def rh_pole_floor_counterexample():
    # At horizontal displacement 1/3 the alleged -1/a^2 >= -4 fails.
    delta = Fraction(1, 3)
    term = -1 / (delta * delta)
    assert term == -9 and term < -4
    return {"delta": str(delta), "local_pole_term": str(term)}

def rh_far_density_threshold_control():
    # Only a scalar sanity check: not an estimate over actual zeta zeros.
    # The attachment asserts positivity for *all* t > 14.13.
    t = 15.0
    value = log(t / (2 * pi)) / (2 * pi) - 4
    assert t > 14.13 and value < 0
    return {"t": t, "proposed_lower_bound": value, "positive": False}

def rh_first_gamma_not_positive_control():
    # Positive 2-point weights suffice to reject a claimed generic sign.
    gamma0, gamma1 = Fraction(1), Fraction(2)
    mean_square = (gamma0**2 + gamma1**2) / 2
    coefficient = gamma0**5 - mean_square * gamma0**3
    assert coefficient == Fraction(-3,2)
    assert coefficient < 0
    return {"first_gamma": str(gamma0),
            "mean_gamma_square": str(mean_square),
            "first_mode_signed_fifth": str(coefficient)}

def ns_r854_exact_conditional_integral():
    # The bound is valid ONLY IF the original real Galerkin rate satisfies
    # |rate(t)-r0| <= L*t on [0,T]. This checks the terminal arithmetic.
    r0 = Fraction(-28273644, 125)
    L = 391309593930357307785216
    T = Fraction(226189, 3938540454339300631433585885184)
    upper = r0*T + Fraction(L,2)*T*T
    expected = Fraction(-128735420172278725243,
        9910376049473991249648549085109551104000)
    assert upper == expected and upper < 0
    # Negative r(0) alone is INSUFFICIENT: r(t)=r0+4|r0|t/T.
    positive_countermodel = abs(r0)*T
    assert positive_countermodel > 0
    return {"strict_conditional_integral_upper":str(upper),
            "initial_negative_alone_positive_integral":str(positive_countermodel),
            "actual_real_ode_rate_certified":False}

def bsd_selected_curve_local_controls():
    # Selected curve is 32a2, not an arbitrary isogenous model.
    x = 39
    rhs = x*(x-1)*(x+1)
    assert rhs == 59280 and rhs == 16*3705
    assert 3705 % 8 == 1  # odd 2-adic unit square criterion
    assert (x-1) % 4 == 2  # v2(x-1) == 1
    original_torsion = ((1,1),(-1,-1),(1,2),(-1,-2))
    attachment_torsion = ((1,1),(2,2),(-1,-2),(-2,1))
    assert original_torsion != attachment_torsion
    # Sha[2]=0 does not imply Sha=0: Z/3 has no 2-torsion.
    assert all((2*a) % 3 != 0 for a in (1,2))
    return {"x":x,"curve_rhs":rhs,"v2_x_minus_1":1,
            "torsion":original_torsion,
            "sha2_trivial_does_not_imply_sha_trivial":True}

def ym_common_carrier_tv_negative_control():
    P=(Fraction(3,4), Fraction(1,4))
    Q=(Fraction(1,2), Fraction(1,2))
    F=(Fraction(1), Fraction(0))
    def mean(p,a):
        return sum(p[i]*a[i] for i in range(2))
    eF_P=mean(P,F)
    eF_Q=mean(Q,F)
    covP=eF_P-eF_P**2
    covQ=eF_Q-eF_Q**2
    tv=sum(abs(P[i]-Q[i]) for i in range(2))/2
    assert tv==Fraction(1,4)
    assert covQ==Fraction(1,4) and covP==Fraction(3,16)
    assert abs(covP-covQ)==Fraction(1,16)<=3*tv
    # Repeating fixed P,Q at every cutoff makes TV remain 1/4.
    return {"same_carrier_tv":str(tv),
            "nonzero_covariance_mismatch":str(abs(covP-covQ)),
            "cutoff_uniform_decay_from_finite_source_alone":False}

def run():
    return {"schema":"dashi-abc-countermodel-tests-v1",
            "claims":{
                "RH_PoleFloor":rh_pole_floor_counterexample(),
                "RH_Threshold":rh_far_density_threshold_control(),
                "RH_FirstGamma":rh_first_gamma_not_positive_control(),
                "NS_R854":ns_r854_exact_conditional_integral(),
                "BSD_Kummer":bsd_selected_curve_local_controls(),
                "YM_R445":ym_common_carrier_tv_negative_control()},
            "agda_kernel_checked":False,
            "clay_endpoint_proved":False}

if __name__=="__main__":
    import json
    print(json.dumps(run(),indent=2))
