import math

from commercial_confinement_probe import (
    greenwald_density_m3,
    greenwald_fraction,
    net_electric_mw,
    strictly_dominates,
    weakly_dominates,
)


def close(a, b, rtol=1e-12):
    assert math.isclose(a, b, rel_tol=rtol, abs_tol=0.0), (a, b)


def test_greenwald():
    # nG[1e20 m^-3] = Ip[MA]/(pi a[m]^2)
    close(greenwald_density_m3(1.0, 1.0), 1e20 / math.pi)
    close(greenwald_fraction(1e20 / math.pi, 1.0, 1.0), 1.0)


def test_net_electric():
    assert net_electric_mw(500.0, [40, 25, 10, 15, 30]) == 380.0


def test_pareto():
    axes = {"net_electric": "max", "recirc": "min", "availability": "max"}
    candidate = {"net_electric": 300, "recirc": 90, "availability": 0.80}
    reference = {"net_electric": 250, "recirc": 100, "availability": 0.75}
    assert weakly_dominates(candidate, reference, axes)
    assert strictly_dominates(candidate, reference, axes)
    assert not weakly_dominates(reference, candidate, axes)


if __name__ == "__main__":
    test_greenwald()
    test_net_electric()
    test_pareto()
    print("ok")
