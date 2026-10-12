from __future__ import annotations

from collections import Counter
from decimal import Decimal, getcontext
from itertools import permutations, product
import numpy as np

getcontext().prec = 50
P = 3
POINTS = list(product(range(3), repeat=3))
INDEX = {p: i for i, p in enumerate(POINTS)}


def q(p):
    x, y, z = p
    return (((x + z) % 3) ** 2 + (y * y) % 3) % 3


def rho(p):
    return {0: 0, 1: 1, 2: -1}[q(p)]


def rank3(m):
    a = np.array(m, dtype=int) % 3
    r = 0
    for col in range(a.shape[1]):
        pivot = next((i for i in range(r, a.shape[0]) if a[i, col]), None)
        if pivot is None:
            continue
        a[[r, pivot]] = a[[pivot, r]]
        if a[r, col] == 2:
            a[r] = 2 * a[r] % 3
        for i in range(a.shape[0]):
            if i != r and a[i, col]:
                a[i] = (a[i] - a[i, col] * a[r]) % 3
        r += 1
    return r


def gl3():
    for entries in product(range(3), repeat=9):
        m = np.array(entries, dtype=int).reshape(3, 3)
        if rank3(m) == 3:
            yield m


def q_isometries():
    out = []
    for m in gl3():
        if all(q(tuple((m @ np.array(p)) % 3)) == q(p) for p in POINTS):
            out.append(m)
    return out


def connection_torus():
    out = set()
    for i in range(3):
        for s in (1, 2):
            v = [0, 0, 0]
            v[i] = s
            out.add(tuple(v))
    return out


def connection_nonsingular():
    return {p for p in POINTS if p != (0, 0, 0) and q(p) != 0}


def preserves_connection(m, connection):
    return {tuple((m @ np.array(v)) % 3) for v in connection} == connection


def orbit_neighbor_profiles(connection):
    profiles = {}
    for cls in (0, 1, 2):
        seen = set()
        for p in [x for x in POINTS if q(x) == cls]:
            counts = [0, 0, 0]
            for d in connection:
                r = tuple((p[k] + d[k]) % 3 for k in range(3))
                counts[q(r)] += 1
            seen.add(tuple(counts))
        profiles[cls] = seen
    return profiles


def finite_potential(p):
    return Decimal(rho(p)) / Decimal(27)


def verify():
    isos = q_isometries()
    torus = connection_torus()
    intrinsic = connection_nonsingular()
    torus_preservers = [m for m in isos if preserves_connection(m, torus)]
    intrinsic_preservers = [m for m in isos if preserves_connection(m, intrinsic)]

    assert Counter(q(p) for p in POINTS) == Counter({0: 3, 1: 12, 2: 12})
    assert len(isos) == 144
    assert len(torus_preservers) == 8
    assert len(intrinsic) == 24
    assert len(intrinsic_preservers) == 144
    assert orbit_neighbor_profiles(intrinsic) == {
        0: {(0, 12, 12)},
        1: {(3, 9, 12)},
        2: {(3, 12, 9)},
    }

    # Degree-24 Laplacian: L phi = rho with phi = rho/27.
    for p in POINTS:
        lhs = Decimal(24) * finite_potential(p)
        lhs -= sum(
            finite_potential(tuple((p[k] + d[k]) % 3 for k in range(3)))
            for d in intrinsic
        )
        assert lhs == Decimal(rho(p))
    assert sum(finite_potential(p) for p in POINTS) == 0

    # Clock diagnostic for the tensor-product interpolation at a maximal
    # vertical derivative grid point: phi=-1/27, d_z phi=4/27.
    edge_mm = Decimal(299792458) / Decimal(9192631770) * Decimal(1000)
    theory = Decimal("1.09e-19")
    phi = -Decimal(1) / Decimal(27)
    dphi = Decimal(4) / Decimal(27)

    def clock_gradient(depth):
        eps = Decimal(1) / (Decimal(3) ** depth)
        return abs(eps * dphi / (Decimal(1) + eps * phi)) / edge_mm

    g35, g36, g37 = (clock_gradient(n) for n in (35, 36, 37))
    assert g36 / theory < Decimal("0.30")
    assert abs(g35 - theory) < abs(g36 - theory)

    return {
        "q_class_counts": {0: 3, 1: 12, 2: 12},
        "q_isometry_group_order": len(isos),
        "torus_adjacency_isometry_count": len(torus_preservers),
        "intrinsic_degree": len(intrinsic),
        "intrinsic_adjacency_isometry_count": len(intrinsic_preservers),
        "intrinsic_potential": "phi = rho/27",
        "rho_interpolation": "(9*x^2*y^2*z^2 - 6*x^2*y^2 - 3*x^2*z^2 + 2*x^2 - 3*x*y^2*z + x*z - 6*y^2*z^2 + 2*y^2 + 2*z^2)/2",
        "depth35_gradient": g35,
        "depth36_gradient": g36,
        "depth37_gradient": g37,
        "depth36_theory_ratio": g36 / theory,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
