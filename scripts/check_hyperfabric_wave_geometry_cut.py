#!/usr/bin/env python3
"""Exact 27-site finite Fourier / signed-zero / lattice mismatch experiment.

Source boundaries: Base369Ternary27HypervoxelFabricGeometryExact and
BalancedTernaryFourierModeExact encode DIFFERENT adjacency geometries.
These checks are finite mathematics, not quantum/string/GR/Clay physics.
Eisenstein integer pair (a,b) means a+b*omega, omega^2+omega+1=0.
"""
from itertools import product

SITES = tuple(product((-1, 0, 1), repeat=3))
ZERO_PHASES = ("-0", "0", "+0")
ZERO, ONE, OMEGA, OMEGA2 = (0, 0), (1, 0), (0, 1), (-1, -1)
ROOTS = (ONE, OMEGA, OMEGA2)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0] - a[1] * b[1])


def sum_exact(items):
    result = ZERO
    for x in items:
        result = add(result, x)
    return result


def chi(k, x):
    return ROOTS[sum(a * b for a, b in zip(k, x)) % 3]


def graph_edges(periodic=False):
    result = set()
    for x in SITES:
        for axis in range(3):
            if periodic or x[axis] != 1:
                y = list(x)
                y[axis] = ((x[axis] + 2) % 3) - 1 if periodic else x[axis] + 1
                result.add(frozenset((x, tuple(y))))
    return result


def graph_laplacian(f, x, edges):
    result = ZERO
    for edge in edges:
        if x in edge:
            y = next(iter(edge - {x}))
            result = add(result, add(f(x), (-f(y)[0], -f(y)[1])))
    return result


def forward(field):
    return {k: sum_exact(mul(field[x], chi(tuple(-a for a in k), x))
                         for x in SITES) for k in SITES}


def inverse_exact(spectrum):
    result = {}
    for x in SITES:
        s = sum_exact(mul(spectrum[k], chi(k, x)) for k in SITES)
        assert s[0] % 27 == 0 and s[1] % 27 == 0
        result[x] = s[0] // 27, s[1] // 27
    return result


def worldsheet_energy(embed):
    worldsheet = tuple(product(range(3), repeat=2))
    edges = set()
    for x in worldsheet:
        for axis in range(2):
            y = list(x)
            y[axis] = (y[axis] + 1) % 3
            edges.add(frozenset((x, tuple(y))))
    return sum(sum((embed[x][j] - embed[y][j]) ** 2 for j in range(3))
               for x, y in (tuple(e) for e in edges))


def test():
    assert len(SITES) == 27
    assert len(set(ZERO_PHASES)) == 3
    assert len({0 for _ in ZERO_PHASES}) == 1
    assert add(ONE, add(OMEGA, OMEGA2)) == ZERO
    assert mul(OMEGA, OMEGA) == OMEGA2
    assert mul(OMEGA, OMEGA2) == ONE
    path = graph_edges()
    torus = graph_edges(periodic=True)
    assert len(path) == 54 and len(torus) == 81
    assert sum((-1, -1, -1) in e for e in path) == 3
    assert sum((0, 0, 0) in e for e in path) == 6
    assert all(sum(x in e for e in torus) == 6 for x in SITES)
    for k in SITES:
        assert sum_exact(chi(k, x) for x in SITES) == (
            (27, 0) if k == (0, 0, 0) else ZERO)
        for x in SITES:
            translated = (((x[0] + 2) % 3) - 1, x[1], x[2])
            assert chi(k, translated) == mul(chi(k, x), ROOTS[k[0] % 3])
            eigenvalue = 3 * sum(component != 0 for component in k)
            assert graph_laplacian(lambda p: chi(k, p), x, torus) == mul(
                (eigenvalue, 0), chi(k, x))
    k, corner = (1, 0, 0), (-1, -1, -1)
    assert graph_laplacian(lambda p: chi(k, p), corner, path) != mul(
        (3, 0), chi(k, corner))
    field = {x: (2 * x[0] - x[1], 1 + x[2]) for x in SITES}
    assert inverse_exact(forward(field)) == field
    const = {x: (0, 0, 0) for x in product(range(3), repeat=2)}
    varied = {x: (x[0], x[1], 0) for x in const}
    assert worldsheet_energy(const) == 0 and worldsheet_energy(varied) > 0
    print("PASS signed-zero noninjective scalar quotient")
    print("PASS 27-site exact Eisenstein character orthogonality and Fourier inversion")
    print("PASS 81-edge periodic-wave eigenmodes at every site")
    print("PASS 54-edge path-voxel operator mismatch, explicit failed eigenmode")
    print("PASS toy 2D worldsheet embedding energy")
    print("BOUNDARY no quantum Hilbert/physical string/GR/Clay promotion")


if __name__ == "__main__":
    test()
