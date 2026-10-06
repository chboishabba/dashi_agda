from triadic_phase_projector_probe import (
    first_surviving_harmonic,
    phase_filter,
    projector_residual_bound_from_coefficients,
    pure_triadic_sector_count,
)


def test_c3_filters_nonmultiples():
    assert abs(phase_filter(3, 1)) < 1e-12
    assert abs(phase_filter(3, 2)) < 1e-12
    assert abs(phase_filter(3, 3) - 1.0) < 1e-12


def test_c9_pushes_first_surviving_harmonic_to_nine():
    assert first_surviving_harmonic(9, range(1, 20)) == 9
    assert abs(phase_filter(9, 3)) < 1e-12
    assert abs(phase_filter(9, 9) - 1.0) < 1e-12


def test_pure_triadic_counts():
    assert pure_triadic_sector_count(1) == 3
    assert pure_triadic_sector_count(2) == 9
    assert pure_triadic_sector_count(3) == 27


def test_residual_bound_keeps_only_multiple_modes():
    coefficients = {1: 0.2, 2: 0.1, 3: 0.05, 6: 0.01, 9: 0.001}
    assert abs(projector_residual_bound_from_coefficients(3, coefficients) - 0.061) < 1e-12
    assert abs(projector_residual_bound_from_coefficients(9, coefficients) - 0.001) < 1e-12


if __name__ == "__main__":
    test_c3_filters_nonmultiples()
    test_c9_pushes_first_surviving_harmonic_to_nine()
    test_pure_triadic_counts()
    test_residual_bound_keeps_only_multiple_modes()
    print("ok")
