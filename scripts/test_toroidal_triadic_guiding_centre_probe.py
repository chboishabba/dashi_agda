from toroidal_triadic_guiding_centre_probe import (
    cyclic_radial_curvature_drift_residual,
    single_phase_radial_curvature_drift_rms,
)


def test_c3_suppresses_radial_curvature_drift_at_aspect_three():
    single = single_phase_radial_curvature_drift_rms(3.0, 1.0, 1, 1200)
    c3 = cyclic_radial_curvature_drift_residual(3.0, 1.0, 1, 3, 1200)
    assert c3 < single * 0.05


def test_c9_strongly_improves_over_c3_at_aspect_three():
    c3 = cyclic_radial_curvature_drift_residual(3.0, 1.0, 1, 3, 1200)
    c9 = cyclic_radial_curvature_drift_residual(3.0, 1.0, 1, 9, 1200)
    assert c9 < c3 * 1e-3


def test_c27_reaches_numerical_floor_for_probe_family():
    c27 = cyclic_radial_curvature_drift_residual(3.0, 1.0, 1, 27, 1200)
    assert c27 < 1e-8


def test_c3_relative_residual_falls_with_aspect_ratio():
    low = cyclic_radial_curvature_drift_residual(3.0, 1.0, 1, 3, 1000)
    high = cyclic_radial_curvature_drift_residual(8.0, 1.0, 1, 3, 1000)
    assert high < low * 0.1


if __name__ == "__main__":
    test_c3_suppresses_radial_curvature_drift_at_aspect_three()
    test_c9_strongly_improves_over_c3_at_aspect_three()
    test_c27_reaches_numerical_floor_for_probe_family()
    test_c3_relative_residual_falls_with_aspect_ratio()
    print("ok")
