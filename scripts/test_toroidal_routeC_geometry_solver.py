import numpy as np

from toroidal_routeC_geometry_solver import (
    RouteCGeometryProblem,
    abc_residual,
    exact_ab_alpha,
    firehose_margin_fraction,
)


def test_unified_ab_exact_closure_and_positive_margin():
    for m in (0.25, 0.5, 0.7, 0.9):
        alpha = exact_ab_alpha(m)
        assert abs(abc_residual(m, alpha)) < 1e-14
        assert firehose_margin_fraction(alpha) > 0.0


def test_route_c_optimizer_improves_declared_objective():
    problem = RouteCGeometryProblem(nth=28, nz=32)
    baseline = problem.objective(np.zeros(4))
    result = problem.optimize(maxiter=450)
    assert result.fun < baseline


def test_route_c_stream_field_divergence_stays_small():
    problem = RouteCGeometryProblem(nth=28, nz=32)
    result = problem.optimize(maxiter=450)
    metrics = problem.metrics(result.x)
    # Finite-difference replay residual; continuum surface divergence is structural.
    assert metrics.surface_divergence_rms < 0.03


if __name__ == "__main__":
    test_unified_ab_exact_closure_and_positive_margin()
    test_route_c_optimizer_improves_declared_objective()
    test_route_c_stream_field_divergence_stays_small()
    print("ok")
