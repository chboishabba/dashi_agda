import math

from commercial_confinement_probe import (
    greenwald_density_m3,
    greenwald_fraction,
    net_electric_mw,
    pareto_frontier,
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


def test_frontier():
    axes = {"net_electric": "max", "recirc": "min"}
    points = [
        {"name": "dominated", "net_electric": 200, "recirc": 120},
        {"name": "balanced", "net_electric": 250, "recirc": 100},
        {"name": "high_net", "net_electric": 300, "recirc": 120},
        {"name": "low_recirc", "net_electric": 220, "recirc": 80},
    ]
    front = pareto_frontier(points, axes)
    assert [point["name"] for point in front] == ["balanced", "high_net", "low_recirc"]


if __name__ == "__main__":
    test_greenwald()
    test_net_electric()
    test_pareto()
    test_frontier()
    print("ok")
