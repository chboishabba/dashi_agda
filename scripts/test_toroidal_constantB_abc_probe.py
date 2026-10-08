import math

from toroidal_constantB_abc_probe import (
    alfvenic_inertia_minus_tension,
    cgl_tension_residual,
    circular_seed_geodesic_curvature_rms,
    firehose_margin,
    inverse_phase,
)


def test_route_a_exact_identity():
    for B2, mu0, rho in [(1.0, 1.0, 1.0), (25.0, 4e-7 * math.pi, 2.3)]:
        assert abs(alfvenic_inertia_minus_tension(B2, mu0, rho)) < 1e-10 * max(1.0, B2 / mu0)


def test_route_b_exact_but_firehose_marginal():
    B2 = 9.0
    mu0 = 2.0
    delta_p = B2 / mu0
    assert abs(cgl_tension_residual(B2, mu0, delta_p)) < 1e-14
    assert abs(firehose_margin(B2, mu0, delta_p)) < 1e-14
    assert firehose_margin(B2, mu0, 0.9 * delta_p) > 0.0


def test_route_c_current_circular_seed_is_not_geodesic():
    rms = circular_seed_geodesic_curvature_rms(
        R0=3.0, r=1.0, B0=1.0, C=0.5, samples=8000, ds=1e-3
    )
    assert rms > 0.1


def test_c3_inversion_fixed_plus_inverse_pair():
    assert inverse_phase(0) == 0
    assert inverse_phase(1) == 2
    assert inverse_phase(2) == 1
    for p in (0, 1, 2):
        assert inverse_phase(inverse_phase(p)) == p


if __name__ == "__main__":
    test_route_a_exact_identity()
    test_route_b_exact_but_firehose_marginal()
    test_route_c_current_circular_seed_is_not_geodesic()
    test_c3_inversion_fixed_plus_inverse_pair()
    print("ok")
