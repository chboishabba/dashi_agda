import math

from screw_pinch_zero_bounce_probe import equilibrium_residual, mirror_force_parallel


def test_force_balance_exact():
    assert abs(
        equilibrium_residual(r=2.0, Btheta=1.5, mu0=4e-7 * math.pi)
    ) < 1e-12


def test_no_mirror():
    assert mirror_force_parallel(Btheta=1.5, Bz=5.0) == 0.0


if __name__ == "__main__":
    test_force_balance_exact()
    test_no_mirror()
    print("ok")
