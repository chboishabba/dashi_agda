#!/usr/bin/env python3
"""Original periodic-positive-bond finite Vec/gauge codec independent reference.

Diagnostic only. No Agda kernel, continuous Haar, UV/IR, or mass gap.
Wilson/Balaban original geometry; DASHI native enumeration and codec owners.
"""
from fractions import Fraction as F
from itertools import product

ONE = (F(1), F(0), F(0), F(0))
I = (F(0), F(1), F(0), F(0))
J = (F(0), F(0), F(1), F(0))
R = (F(3,5), F(4,5), F(0), F(0))
Q = (ONE, I, J, R, tuple(-v for v in R))


def mul(a, b):
    w,x,y,z = a
    s,p,q,r = b
    return (w*s-x*p-y*q-z*r, w*p+x*s+y*r-z*q,
            w*q-x*r+y*s+z*p, w*r+x*q-y*p+z*s)


def inv(q):
    return (q[0], -q[1], -q[2], -q[3])


def bonds(L):
    # Torus.productFinite(siteFinite, axisFinite): site x axis.
    # siteFinite = (CyclicIndex L)^2 x (CyclicIndex L)^2.
    return [(site, axis) for site in product(range(L), repeat=4)
            for axis in range(4)]


def forward(site, axis, L):
    return tuple((coordinate + (index == axis)) % L
                 for index, coordinate in enumerate(site))


def test(L):
    names = bonds(L)
    assert len(names) == 4 * L**4
    assert len(set(names)) == len(names)
    field = {bond: Q[(11*bond[0][0] + 7*bond[0][1] +
                      5*bond[0][2] + 3*bond[0][3] + bond[1]) % len(Q)]
             for bond in names}
    encoded = tuple(field[bond] for bond in names)
    decoded = dict(zip(names, encoded))
    assert decoded == field
    assert tuple(decoded[bond] for bond in names) == encoded
    gauge = {site: Q[(3*site[0] + 2*site[1] + site[2] + site[3] + 3) % len(Q)]
             for site in product(range(L), repeat=4)}
    left = [gauge[site] for site, axis in names]
    right = [inv(gauge[forward(site, axis, L)]) for site, axis in names]
    # one-link bilateral Haar coordinates: gamma(x)*(U*gamma(y)^-1)
    v_gauge = tuple(mul(l, mul(u, r))
                    for l, u, r in zip(left, encoded, right))
    # Original native bond transform: (gamma(x)*U)*gamma(y)^-1.
    native = {bond: mul(mul(gauge[bond[0]], field[bond]),
                        inv(gauge[forward(bond[0], bond[1], L)]))
              for bond in names}
    assert tuple(native[bond] for bond in names) == v_gauge
    bad = tuple(mul(l, mul(u, gauge[forward(site, axis, L)]))
                for ((site, axis), l, u) in zip(names, left, encoded))
    wrong = sum(1 for x, y in zip(bad, v_gauge) if x != y)
    assert wrong > 0
    return {'side': L, 'sites': L**4, 'positive_links': len(names),
            'pointwise_roundtrips': len(names), 'gauge_naturality_matches': len(names),
            'wrong_target_inverse_rejected': wrong}


def main():
    for L in (2, 3, 4):
        print(test(L))
    # A repeated-label enumeration cannot recover independently assigned entries.
    duplicate = [((0,0,0,0), 0)] * 2
    two_values = [ONE, I]
    assert [dict(zip(duplicate, two_values))[bond] for bond in duplicate] != two_values
    print({'duplicate_free_negative_control': 'PASS', 'scope': 'finite reference only'})


if __name__ == '__main__':
    main()
