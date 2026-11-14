import math
import numpy as np

from toroidal_constantB_clebsch_probe import (
    divergence_residual,
    fieldline_one_poloidal_turn,
    lorentz_components,
    magnitude,
    phase_project,
)


def test_constant_magnitude_and_divergence_free():
    for theta in np.linspace(0.0, 2.0 * math.pi, 33):
        assert abs(magnitude(3.0, 1.0, float(theta), 1.0, 1.0) - 1.0) < 1e-12
        assert divergence_residual(3.0, 1.0, float(theta), 1.0, 1.0) == 0.0


def test_static_isotropic_equilibrium_obstruction_is_nontrivial():
    tangential = []
    for theta in np.linspace(0.1, 6.1, 61):
        _, ftheta, fzeta = lorentz_components(3.0, 1.0, float(theta), 1.0, 1.0)
        tangential.append(abs(ftheta) + abs(fzeta))
    assert max(tangential) > 1e-3


def test_full_poloidal_turn_radial_curvature_average_closes():
    _, radial, avg, rms = fieldline_one_poloidal_turn(samples=6913)
    assert abs(avg) < 1e-10
    assert rms > 0.1  # closure is orbital/cyclic, not pointwise zero curvature drift
    samples = radial[:-1]  # remove duplicated periodic endpoint: 6912=256*27
    c3 = phase_project(samples, 3)
    c9 = phase_project(samples, 9)
    c27 = phase_project(samples, 27)
    rms3 = math.sqrt(float(np.mean(c3 * c3)))
    rms9 = math.sqrt(float(np.mean(c9 * c9)))
    rms27 = math.sqrt(float(np.mean(c27 * c27)))
    assert rms9 < rms3
    assert rms27 < rms9


if __name__ == "__main__":
    test_constant_magnitude_and_divergence_free()
    test_static_isotropic_equilibrium_obstruction_is_nontrivial()
    test_full_poloidal_turn_radial_curvature_average_closes()
    print("ok")
