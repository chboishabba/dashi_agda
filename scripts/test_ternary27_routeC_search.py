import math
import numpy as np

from ternary27_routeC_search import Ternary27RouteC, c3_basis


def test_literal_chart_has_twenty_seven_coordinates():
    problem = Ternary27RouteC(nth=12, nz=15)
    assert len(problem.free_idx) == 24
    assert problem.embed(np.zeros(24)).shape == (27,)


def test_c3_basis_is_toroidally_periodic_under_two_pi_over_three_shift():
    theta = np.array([[0.2, 1.1], [2.0, 2.8]])
    zeta = np.array([[0.4, 0.8], [1.7, 2.3]])
    left = c3_basis(theta, zeta)
    right = c3_basis(theta, zeta + 2*math.pi/3)
    assert np.max(np.abs(left-right)) < 1e-12


def test_stream_field_has_small_surface_divergence_replay_residual():
    problem = Ternary27RouteC(nth=20, nz=24)
    coeff = np.zeros(27)
    coeff[19] = 0.03
    coeff[23] = -0.02
    metrics = problem.metrics(coeff)
    assert metrics["surface_divergence_rms"] < 1e-3


def test_short_continuation_stays_geometrically_admissible():
    problem = Ternary27RouteC(nth=14, nz=18)
    rows = problem.continuation(levels=(0.0, 0.5, 1.0), maxiter=35)
    assert len(rows) == 3
    for _, _, metrics, coeff in rows:
        assert coeff.shape == (27,)
        assert metrics["minimum_minor_radius"] > 0.35
        assert math.isfinite(metrics["relative_B_spread"])
        assert math.isfinite(metrics["geodesic_curvature_rms"])
        assert metrics["surface_divergence_rms"] < 5e-3


if __name__ == "__main__":
    test_literal_chart_has_twenty_seven_coordinates()
    test_c3_basis_is_toroidally_periodic_under_two_pi_over_three_shift()
    test_stream_field_has_small_surface_divergence_replay_residual()
    test_short_continuation_stays_geometrically_admissible()
    print("ok")
