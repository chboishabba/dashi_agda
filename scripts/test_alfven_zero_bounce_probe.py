import math

from alfven_zero_bounce_probe import (
    check_exact_ideal_mhd,
    curvature_magnitude,
    mirror_force_parallel,
)


def test_constant_magnitude_and_exact_mhd():
    out = check_exact_ideal_mhd(
        B0=5.0,
        amp=1.0,
        k=2.0,
        rho=3.0,
        mu0=4e-7 * math.pi,
    )
    assert out["max_Bmag2_error"] < 1e-10
    assert out["max_momentum_residual"] < 1e-9
    assert out["max_induction_residual"] < 1e-9


def test_zero_mirror_force():
    assert abs(mirror_force_parallel(B0=5.0, amp=1.0, k=2.0, rho=3.0)) < 1e-12


def test_curvature_remains_nonzero():
    assert curvature_magnitude(B0=5.0, amp=1.0, k=2.0) > 0.0


if __name__ == "__main__":
    test_constant_magnitude_and_exact_mhd()
    test_zero_mirror_force()
    test_curvature_remains_nonzero()
    print("ok")
