import math

from zero_bounce_triadic_probe import (
    maximum_phase_quantization_error_radians,
    minimum_triadic_depth_for_phase_error,
    mirror_ratio_for_trapped_fraction,
    no_mirror_for_pitch_floor,
    trapped_fraction_isotropic,
    triadic_phase_count,
)


def close(a, b, rtol=1e-12):
    assert math.isclose(a, b, rel_tol=rtol, abs_tol=0.0), (a, b)


def test_static_mirror_fraction():
    assert trapped_fraction_isotropic(1.0) == 0.0
    close(mirror_ratio_for_trapped_fraction(0.1), 1.0 / 0.99)
    close(mirror_ratio_for_trapped_fraction(0.01), 1.0 / 0.9999)
    close(mirror_ratio_for_trapped_fraction(0.001), 1.0 / 0.999999)


def test_declared_pitch_floor():
    assert no_mirror_for_pitch_floor(1.01, 0.2)
    assert not no_mirror_for_pitch_floor(1.01, 0.0)


def test_triadic_resolution():
    assert triadic_phase_count(1) == 3
    assert triadic_phase_count(2) == 9
    assert triadic_phase_count(3) == 27
    close(maximum_phase_quantization_error_radians(1), math.pi / 3)
    close(maximum_phase_quantization_error_radians(2), math.pi / 9)
    close(maximum_phase_quantization_error_radians(3), math.pi / 27)
    assert minimum_triadic_depth_for_phase_error(math.pi / 10) == 3


if __name__ == "__main__":
    test_static_mirror_fraction()
    test_declared_pitch_floor()
    test_triadic_resolution()
    print("ok")
