import numpy as np

from admissible_cone_routeC_search import (
    abc_seed,
    admissible,
    c3n_allowed_harmonic,
    continuation_schedule,
    continuation_states,
    equality_constraints,
    equality_jacobian,
    nullspace,
    projected_descent_direction,
)


def test_abc_continuation_is_exactly_admissible():
    schedule = continuation_schedule(5)
    states = continuation_states(5, mach_share=0.7)
    for state, target in zip(states, schedule):
        assert np.max(np.abs(equality_constraints(state, float(target)))) < 1e-12
        assert admissible(state, float(target))


def test_constraint_nullspace_has_expected_dimension():
    for delta in (0.0, 0.25, 0.5, 0.75, 1.0):
        state = abc_seed(delta)
        J = equality_jacobian(state)
        N = nullspace(J)
        assert N.shape == (7, 5)
        assert np.linalg.norm(J @ N) < 1e-12


def test_projected_direction_is_tangent():
    state = abc_seed(0.5)
    gradient = np.array([1.0, -2.0, 3.0, 4.0, -1.0, 0.5, 2.0])
    direction = projected_descent_direction(state, gradient)
    assert np.linalg.norm(equality_jacobian(state) @ direction) < 1e-12


def test_triadic_harmonic_filter():
    assert c3n_allowed_harmonic(3, 1)
    assert c3n_allowed_harmonic(9, 1)
    assert c3n_allowed_harmonic(9, 2)
    assert not c3n_allowed_harmonic(3, 2)
    assert c3n_allowed_harmonic(27, 3)
    assert not c3n_allowed_harmonic(9, 3)


if __name__ == "__main__":
    test_abc_continuation_is_exactly_admissible()
    test_constraint_nullspace_has_expected_dimension()
    test_projected_direction_is_tangent()
    test_triadic_harmonic_filter()
    print("ok")
