#!/usr/bin/env python3
"""Exact R829/R830 -> R854 rational affine upper bound regression.

On the original selected 3-4-5 snapshot, r(0)=-28273644/125.
R828 supplies L=391309593930357307785216 for the finite Fourier
REAL ODE and T=226189/3938540454339300631433585885184.
IF the exact R850/R853 signed rate follows the same real Galerkin
ODE and obeys r(t)<=r(0)+L*t, then integrating proves
I(T)<=r(0)*T+L*T*T/2<0, strictly better than prior R830 bound.

No new proof of the REAL ODE carrier, Lipschitz inequality or the
R408-to-real flow same-object identification is claimed here.
This script checks the entire scalar arithmetic with fractions.
"""
import json
from fractions import Fraction as Q

SOURCE_RATE = Q(-28273644, 125)
L = Q(391309593930357307785216)
T = Q(226189, 3938540454339300631433585885184)
COARSE_UPPER = Q(-226189, 2)


def main():
    assert T > 0 and L > 0 and SOURCE_RATE < 0
    envelope_terminal = SOURCE_RATE + L*T
    integrated = SOURCE_RATE*T + L*T*T/2
    old = COARSE_UPPER*T
    assert envelope_terminal < COARSE_UPPER < 0
    assert integrated < old < 0
    # New R855: enormous slack in the *actual fixed* R830 horizon.
    # These two weaker budgets can replace the sharp R828 constant IF
    # proved for the physical original R853 rate along a real solution.
    weak_pointwise = 10_000_000 * L
    weak_integrated = 20_000_000 * L
    assert SOURCE_RATE + weak_pointwise*T < 0
    assert SOURCE_RATE*T + weak_integrated*T*T/2 < 0
    exact_pointwise_threshold = -SOURCE_RATE/T
    exact_integrated_threshold = -2*SOURCE_RATE/T
    assert weak_pointwise < exact_pointwise_threshold
    assert weak_integrated < exact_integrated_threshold
    # Counterexample: the negative INITIAL rate alone says nothing
    # about later integrated sign without the physical Lipschitz bound.
    # A linear scalar with slope 2*abs(r0)/T becomes positive enough
    # for its integral to vanish; a still steeper slope makes it >0.
    wrong_slope = Q(4)*abs(SOURCE_RATE)/T
    assert SOURCE_RATE*T + wrong_slope*T*T/2 > 0
    print(json.dumps({
        "schema":"ns_r854_same_source_affine_integral_rational_v1",
        "original_initial_rate":str(SOURCE_RATE),
        "source_R828_rate_Lipschitz_bound":str(L),
        "source_horizon":str(T),
        "new_terminal_upper":str(envelope_terminal),
        "old_R830_constant_upper":str(COARSE_UPPER),
        "new_affine_integral_upper":str(integrated),
        "old_R830_integral_upper":str(old),
        "strictly_stronger_and_negative":True,
        "negative_initial_rate_alone_not_enough":True,
        "R855_pointwise_weak_L_factor":10_000_000,
        "R855_integrated_weak_L_factor":20_000_000,
        "R855_exact_pointwise_derivative_budget":str(exact_pointwise_threshold),
        "R855_exact_integrated_derivative_budget":str(exact_integrated_threshold),
        "R855_weak_pointwise_terminal":str(SOURCE_RATE+weak_pointwise*T),
        "R855_weak_integrated_upper":str(SOURCE_RATE*T+weak_integrated*T*T/2),
        "actual_R853_weak_rate_bound_proved":False,
        "real_time_selected_R408_trajectory_built":False,
        "original_physical_Lipschitz_proved_in_Agda":False,
        "ns_clay_promotion":False,
    }, indent=2))


if __name__ == "__main__":
    main()
