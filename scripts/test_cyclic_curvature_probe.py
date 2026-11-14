import math

from cyclic_curvature_probe import (
    triad_vectors,
    vector_sum,
    triadic_children_sum_zero,
    torus_helix_radial_curvature_mean,
)


def test_equal_phase_triad_closes():
    sx, sy = vector_sum(triad_vectors(1.0))
    assert abs(sx) < 1e-12
    assert abs(sy) < 1e-12


def test_recursive_triadic_children_close():
    assert triadic_children_sum_zero(1.0, depth=4)


def test_naive_torus_helix_does_not_cancel_radial_curvature():
    value = torus_helix_radial_curvature_mean(R=3.0, r=1.0, m=3, samples=1200)
    assert abs(value) > 0.1


if __name__ == "__main__":
    test_equal_phase_triad_closes()
    test_recursive_triadic_children_close()
    test_naive_torus_helix_does_not_cancel_radial_curvature()
    print("ok")
