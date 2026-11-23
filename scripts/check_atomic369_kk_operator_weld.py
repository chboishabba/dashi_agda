#!/usr/bin/env python3
"""MG06 reference: finite gauge covariance and radial atomic operator identity.

Mathematical finite fixture only, not a physical 5D KK -> QED derivation.
"""
import sympy as s
from itertools import product


def link_laplacian(n, edges, links):
    h = s.zeros(n)
    for i, j in edges:
        u = links[i, j]  # here U_ij = +/-1 = inverse(U_ij)
        h[i, i] += 1
        h[j, j] += 1
        h[i, j] -= u
        h[j, i] -= u
    return h


def radial(n, dr, z, mu, ell):
    # u(r)=r*R(r); atomic units, hard Dirichlet radial boundaries.
    rs = [(i + 1) * dr for i in range(n)]
    h = s.diag(*[
        1 / (mu * dr**2) + s.Rational(ell * (ell + 1), 2) / (mu * r**2) - z / r
        for r in rs
    ])
    off = -s.Rational(1, 2) / (mu * dr**2)
    for i in range(n - 1):
        h[i, i + 1] = off
        h[i + 1, i] = off
    return h


def main():
    n = 9
    edges = [(i, (i + 1) % n) for i in range(n)]
    links = {e: s.Integer(1) for e in edges}
    h = link_laplacian(n, edges, links)
    assert h * s.ones(n, 1) == s.zeros(n, 1)
    for signs in product((-1, 1), repeat=n):
        d = s.diag(*signs)
        changed = {(i, j): signs[i] * u * signs[j] for (i, j), u in links.items()}
        assert link_laplacian(n, edges, changed) == d * h * d
    flux = links.copy()
    flux[edges[0]] = s.Integer(-1)
    hflux = link_laplacian(n, edges, flux)
    assert s.prod(links.values()) == 1 and s.prod(flux.values()) == -1
    assert h.det() == 0 and hflux.det() != 0
    mu = s.Rational(1836, 1837)  # illustrative rational, NOT CODATA
    dr = s.Rational(1, 4)
    for z in (1, 2):
        for ell in (0, 1):
            hrad = radial(8, dr, z, mu, ell)
            kin = radial(8, dr, 0, mu, ell)
            coul = s.diag(*[-s.Rational(z, 1) / ((i + 1) * dr) for i in range(8)])
            assert hrad == kin + coul and hrad == hrad.T
    assert radial(8, dr, 1, mu, 0) != radial(8, dr, 1, s.Integer(1), 0)
    # Source-owned constants are inputs, not outputs of the KK fixture.
    hartree_ev, ratio = 27.211386245981, 5.446170214889e-4
    assert abs(0.5 * hartree_ev / (1 + ratio) - 13.598287264283275) < 1e-12
    print("PASS 512 gauge-frame conjugacies; holonomy distinction; 4 exact radial decompositions; original hydrogen input")
    print("OPEN same-action KK electron, physical coupling, QED/spin and continuum atomic operator")


if __name__ == "__main__":
    main()
