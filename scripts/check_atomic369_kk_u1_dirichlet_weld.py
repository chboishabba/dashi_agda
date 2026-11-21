#!/usr/bin/env python3
"""MG06 finite complex-phase gauge and atomic radial Dirichlet weld.
Exact fourth-root U(1) subgroup only; NOT a physical 5D KK/QED derivation.
"""
from itertools import product
import sympy as s

PHASES = (s.Integer(1), s.I, -s.Integer(1), -s.I)

def cycle_hamiltonian(links):
    n = len(links)
    h = s.zeros(n)
    for i, u in enumerate(links):
        j = (i + 1) % n
        h[i, i] += 1
        h[j, j] += 1
        h[i, j] -= u
        h[j, i] -= s.conjugate(u)
    return h

def dirichlet_incidence(n, links=None):
    """n interior nodes plus two zero-Dirichlet boundary edges."""
    if links is None:
        links = (s.Integer(1),) * (n - 1)
    assert len(links) == n - 1
    b = s.zeros(n + 1, n)
    b[0, 0] = 1
    b[n, n - 1] = 1
    for i, u in enumerate(links):
        b[i + 1, i] = 1
        b[i + 1, i + 1] = -u
    return b

def finite_radial(n, dr, z, mu, ell):
    rs = [dr * (i + 1) for i in range(n)]
    h = s.diag(*[
        1 / (mu * dr**2)
        + s.Rational(ell * (ell + 1), 2) / (mu * r**2)
        - s.Rational(z, 1) / r
        for r in rs
    ])
    for i in range(n - 1):
        h[i, i + 1] = -1 / (2 * mu * dr**2)
        h[i + 1, i] = -1 / (2 * mu * dr**2)
    return h

def main():
    n = 4
    covariant = 0
    for base in ((s.Integer(1),) * n,
                 (s.I, s.Integer(1), s.Integer(1), s.Integer(1))):
        h = cycle_hamiltonian(base)
        for g in product(PHASES, repeat=n):
            d = s.diag(*g)
            transformed = tuple(
                g[i] * base[i] * s.conjugate(g[(i + 1) % n])
                for i in range(n))
            assert cycle_hamiltonian(transformed) == d * h * d.conjugate().T
            assert s.prod(transformed) == s.prod(base)
            covariant += 1
    assert covariant == 512
    h0 = cycle_hamiltonian((s.Integer(1),) * n)
    hi = cycle_hamiltonian((s.I, s.Integer(1), s.Integer(1), s.Integer(1)))
    assert h0.det() == 0 and hi.det() != 0
    assert h0.charpoly().as_expr() != hi.charpoly().as_expr()

    n = 8
    b = dirichlet_incidence(n)
    expected = s.diag(*([2] * n))
    for i in range(n - 1):
        expected[i, i + 1] = expected[i + 1, i] = -1
    assert b.H * b == expected
    assert b[:-1, :].H * b[:-1, :] != expected
    tested = 0
    dr = s.Rational(1, 4)
    for z, ell, mu in product(
        (1, 2), (0, 1), (s.Integer(1), s.Rational(1836, 1837))
    ):
        rs = [dr * (i + 1) for i in range(n)]
        centrifugal = s.diag(*[
            s.Rational(ell * (ell + 1), 2) / (mu * r**2) for r in rs
        ])
        coulomb = s.diag(*[-s.Rational(z, 1) / r for r in rs])
        geometric = b.H * b / (2 * mu * dr**2) + centrifugal + coulomb
        assert geometric == finite_radial(n, dr, z, mu, ell)
        assert geometric == geometric.H
        assert geometric != b.H * b / (2 * mu * dr**2) + centrifugal
        tested += 1
    assert tested == 8

    v = s.diag(*[s.Rational(1, (i + 1) * 10) for i in range(n)])
    assert (
        finite_radial(n, dr, 2, s.Integer(1), 0) + v
        == b.T * b / (2 * dr**2)
        + s.diag(*[-2 / (dr * (i + 1)) for i in range(n)]) + v
    )
    assert finite_radial(n, dr, 2, s.Integer(1), 0) + v != finite_radial(
        n, dr, 2, s.Integer(1), 0
    )
    phased = dirichlet_incidence(
        n, (s.I,) + (s.Integer(1),) * (n - 2)
    )
    assert phased.H * phased != b.T * b
    print(
        f"PASS gauge_covariance={covariant}/512 radial_weld={tested}/8; "
        "holonomy, Dirichlet, electrostatic and Hartree-input negative controls"
    )
    print(
        "OPEN physical KK reduction, electron spin/mass/charge, "
        "369-to-operator derivation, continuum atomic spectrum and Agda kernel"
    )

if __name__ == "__main__":
    main()
