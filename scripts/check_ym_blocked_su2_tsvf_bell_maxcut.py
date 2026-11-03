#!/usr/bin/env python3
"""Exact independent R445 blocked SU(2)/Q8 reference and P01 Bell no-go.

Q8 is an explicit noncommuting subgroup of SU(2), used for a finite
counterexample/positive-control regression, not continuous Haar or a proof
about every SU(2) matrix. Agda theorem owners: PathBianchi, PeriodicCoordinate
Closure, NativeBlockedSU2PathHolonomy, RationalSU2ExactGroupLaws, Bell no-go.
"""
from fractions import Fraction as F
from itertools import product

ONE = (1, 0, 0, 0)
I, J, K = (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
Q8 = (ONE, I, J, K, (-1, 0, 0, 0), (0, -1, 0, 0),
      (0, 0, -1, 0), (0, 0, 0, -1))


def multiply(a, b):
    w, x, y, z = a
    v, p, q, r = b
    return (w*v-x*p-y*q-z*r, w*p+x*v+y*r-z*q,
            w*q-x*r+y*v+z*p, w*r+x*q-y*p+z*v)


def inverse(a):
    return (a[0], -a[1], -a[2], -a[3])


def choose(coords, extra):
    key = sum((i+7)*v*v+(17+i)*v for i, v in enumerate(coords))
    return Q8[(key+extra) % 8]


def gauge(coords):
    return choose(coords, 5)


def link(coords, axis):
    return choose(coords, axis*11+3)


def step(coords, axis, side):
    values = list(coords)
    values[axis] = (values[axis]+1) % side
    return tuple(values)


def fine(coarse, offset, L):
    return tuple(c*L+o for c, o in zip(coarse, offset))


def block(coords, L):
    return tuple(v//L for v in coords), tuple(v%L for v in coords)


def holonomy(start, axis, L, side, transformed=False):
    acc, coords = ONE, start
    for _ in range(L):
        dest = step(coords, axis, side)
        u = link(coords, axis)
        if transformed:
            u = multiply(multiply(gauge(coords), u), inverse(gauge(dest)))
        acc = multiply(acc, u)
        coords = dest
    return acc, coords


def verify():
    count = 0
    for M, L in [(1, 1), (2, 1), (1, 3), (2, 2), (2, 3), (3, 2)]:
        side = M * L
        for coarse in product(range(M), repeat=4):
            for offset in product(range(L), repeat=4):
                start = fine(coarse, offset, L)
                assert block(start, L) == (coarse, offset)
                for axis in range(4):
                    raw, end = holonomy(start, axis, L, side)
                    gauged, end2 = holonomy(start, axis, L, side, True)
                    assert end == end2
                    assert gauged == multiply(
                        multiply(gauge(start), raw), inverse(gauge(end)))
                    c2, o2 = block(end, L)
                    target = list(coarse)
                    target[axis] = (target[axis] + 1) % M
                    assert c2 == tuple(target) and o2 == offset
                    if L == 1:
                        assert raw == link(start, axis)
                    count += 1

    # Negative controls: path ordering matters in non-Abelian SU(2).
    assert multiply(I, J) == K
    assert multiply(J, I) == tuple(-x for x in K)

    # Bell correlated-state no-go: identical FULL 2x2 one-site reductions,
    # distinct two-site global states with EXACT ZERO global Born overlap.
    plus, minus = (F(1), F(0), F(0), F(1)), (F(1), F(0), F(0), F(-1))

    def reduce_site(v, which):
        if which == 0:
            return (v[0]*v[0]+v[1]*v[1], v[0]*v[2]+v[1]*v[3],
                    v[2]*v[0]+v[3]*v[1], v[2]*v[2]+v[3]*v[3])
        return (v[0]*v[0]+v[2]*v[2], v[0]*v[1]+v[2]*v[3],
                v[1]*v[0]+v[3]*v[2], v[1]*v[1]+v[3]*v[3])

    for which in (0, 1):
        assert reduce_site(plus, which) == reduce_site(minus, which) == (
            F(1), F(0), F(0), F(1))
    assert sum(x*y for x, y in zip(plus, minus)) == 0
    assert sum(x*x for x in plus) == sum(x*x for x in minus) == 2
    print(f"PASS {count} exact blocked Q8 bond/endpoint/gauge cases, "
          "Bell marginal/global no-go and noncommutative negative control")


if __name__ == "__main__":
    verify()
