#!/usr/bin/env python3
"""MG06 observer/dimension-indexed geometry: finite exact diagnostic.
No physical KK electron or independent Coulomb derivation is claimed.
"""
from itertools import product
import sympy as s

def spectrum_trace(graph):
    if graph == "cube":
        verts = list(product(range(3), repeat=3))
        edges = [(i, j) for i, a in enumerate(verts)
                 for j, b in enumerate(verts)
                 if i < j and sum(abs(x-y) for x, y in zip(a,b)) == 1]
    elif graph == "circle":
        edges = [(i, (i+1) % 27) for i in range(27)]
    else:
        raise ValueError(graph)
    return 2 * len(edges)

def mode_observation(n):
    return n % 27

def mode_energy(n, radius=1):
    return s.Rational(n*n, radius*radius)

def radial_electric_field(d, r):
    # Unit flux outside a point source in d spatial dimensions.
    # Angular-area normalization and source charge deliberately omitted.
    return r**(1-d)

def main():
    assert spectrum_trace("cube") == 108
    assert spectrum_trace("circle") == 54
    aliases = 0
    for k in range(-3, 4):
        for n in range(27):
            assert mode_observation(n) == mode_observation(n + 27*k)
            assert mode_energy(n+27*k) == s.Rational((n+27*k)**2)
            quotient, remainder = divmod(n+27*k, 27)
            assert 27*quotient + remainder == n+27*k
            aliases += 1
    assert mode_observation(0) == mode_observation(27)
    assert mode_energy(0) != mode_energy(27)

    r = s.symbols("r", positive=True)
    for d in (2, 3, 4):
        field = radial_electric_field(d, r)
        assert s.simplify(s.diff(r**(d-1)*field, r)) == 0
    assert s.integrate(radial_electric_field(2, r), r) == s.log(r)
    assert s.integrate(radial_electric_field(3, r), r) == -1/r
    assert s.integrate(radial_electric_field(4, r), r) == -1/(2*r**2)
    charge = s.symbols("charge", real=True)
    assert charge*radial_electric_field(3,r) != radial_electric_field(3,r)

    print(f"PASS {aliases} exact mode alias/reconstruction cases; traces 108 != 54")
    print("PASS 3 dimension-indexed radial flux laws and potentials; source negative control")
    print("OPEN source strength, observer physical realization, KK electron and same-H")

if __name__ == "__main__":
    main()
