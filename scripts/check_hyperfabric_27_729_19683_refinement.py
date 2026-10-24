#!/usr/bin/env python3
"""Exact 27 -> 729 -> 19683 free-Laplacian cylinder test and gauge obstruction.

All equalities use Fraction / integers; no float arithmetic. These are
P3^3, P3^6 and P3^9 PATH-product sites (NOT GF729 multiplication,
Monster's 729-dimensional module, VOA charge eigenspaces or physical strings).
"""
from fractions import Fraction
from itertools import product
from functools import lru_cache

DIGITS = (-1, 0, 1)


def sites(n):
    return product(DIGITS, repeat=n)


def laplace(f, point):
    acc = 0
    for axis in range(len(point)):
        for step in (-1, 1):
            y = list(point)
            y[axis] += step
            if -1 <= y[axis] <= 1:
                acc += f(point) - f(tuple(y))
    return acc


def pullback(f, n):
    return lambda point: f(point[:n])


def average_last(f, keep, total):
    depth = total - keep
    mass = 3 ** depth
    tail_sites = tuple(sites(depth))
    @lru_cache(None)
    def projected(head):
        assert len(head) == keep
        return Fraction(sum(f(head + tail) for tail in tail_sites), mass)
    return projected


def field(point):
    n = len(point)
    return (2 * point[0] - 3 * point[1] + point[2] ** 2
            + 4 * point[-1] + point[0] * point[-1]
            - point[n // 2] ** 2 + 1)


def check_level(keep, total):
    assert total - keep == 3
    assert 3**keep in (27, 729)
    assert 3**total in (729, 19683)
    # R I = identity and L_fine I = I L_coarse on an arbitrary polynomial.
    source = lambda x: (2 * x[0] - x[1] + x[-1] ** 2)
    lift = pullback(source, keep)
    for x in sites(total):
        assert laplace(lift, x) == laplace(source, x[:keep])
    projected_lift = average_last(lift, keep, total)
    for x in sites(keep):
        assert projected_lift(x) == source(x)
    # R L_fine = L_coarse R for non-separable fine field.
    projected = average_last(field, keep, total)
    projected_laplacian = average_last(lambda x: laplace(field, x), keep, total)
    for x in sites(keep):
        assert projected_laplacian(x) == laplace(projected, x)
    print(f"PASS P3^{keep} <-> P3^{total}: RI=1, L I=I L, R L=L R, exact")


def twisted_laplace(f, point, first_new_axis):
    acc = 0
    for axis in range(len(point)):
        for step in (-1, 1):
            y = list(point)
            y[axis] += step
            if -1 <= y[axis] <= 1:
                flipped = (axis == first_new_axis and
                           set((point[axis], y[axis])) == {-1, 0})
                transport = -1 if flipped else 1
                acc += f(point) - transport*f(tuple(y))
    return acc


def check_gauge_obstruction():
    keep, total = 3, 6
    vacuum = lambda _: 1
    coarse = average_last(vacuum, keep, total)
    gauge_avg = average_last(lambda p: twisted_laplace(vacuum, p, keep),
                             keep, total)
    origin = (0,) * keep
    assert laplace(coarse, origin) == 0
    assert gauge_avg(origin) == Fraction(4, 3)
    print("PASS sign-twisted added-edge obstruction: naive R L_A != L R, defect=4/3")


def run():
    check_level(3, 6)
    check_level(6, 9)
    check_gauge_obstruction()
    check_gauge_covariant_repair()
    check_curved_plaquette_flux()
    print("BOUNDARY free graph operators only; selected physical gauge/GR/string/YM/NS remains unpaid")



def gauge_sign(point, first_new_axis):
    # A Z2 gauge choice: + on -1 slice, - on 0,+1 slices.
    # This realizes the *flat* sign twist; no Wilson curvature is implied.
    return 1 if point[first_new_axis] == -1 else -1


def check_gauge_covariant_repair():
    keep, total = 3, 6
    src = lambda x: 3*x[0] - 2*x[1] + x[2]**2 + 1
    fine = lambda x: x[0]*x[3] + 2*x[1] - x[4]**2 + x[5]

    def g(x):
        return gauge_sign(x, keep)

    def covariant_lift(f):
        return lambda x: g(x)*f(x[:keep])

    def covariant_average(f):
        return average_last(lambda x: g(x)*f(x), keep, total)

    lift = covariant_lift(src)
    assert all(twisted_laplace(lift, x, keep) ==
               g(x)*laplace(src, x[:keep]) for x in sites(total))
    projected_lift = covariant_average(lift)
    assert all(projected_lift(x) == src(x) for x in sites(keep))

    # The entire flat twisted operator is conjugate to the ordinary one.
    assert all(twisted_laplace(fine, x, keep) ==
               g(x)*laplace(lambda y: g(y)*fine(y), x)
               for x in sites(total))
    projected = covariant_average(fine)
    projected_L = covariant_average(lambda x: twisted_laplace(fine, x, keep))
    assert all(projected_L(x) == laplace(projected, x)
               for x in sites(keep))
    print("PASS flat Z2 twist: covariant I_A/R_A restore both exact Laplacian squares")


def check_curved_plaquette_flux():
    # One negative edge and three positive edges around a square:
    # genuine nontrivial Z2 Wilson loop, not removable by site signs.
    p = (0, 0, 0, 0, 0, 0)
    q = (0, 0, 0, 1, 0, 0)
    r = (0, 0, 0, 1, 1, 0)
    s = (0, 0, 0, 0, 1, 0)
    loop = (p, q, r, s, p)
    negative = frozenset((p, q))
    def u(a, b):
        return -1 if frozenset((a, b)) == negative else 1
    edges = list(zip(loop, loop[1:]))
    assert all(sum(abs(a[i]-b[i]) for i in range(6)) == 1
               for a, b in edges)
    assert u(p,q)*u(q,r)*u(r,s)*u(s,p) == -1
    # Gauge-invariant Wilson product; exhaustive 2^4 parallel-section no-go.
    for labels in product((-1, 1), repeat=4):
        local = dict(zip((p, q, r, s), labels))
        gauge_product = 1
        satisfied = True
        for a, b in edges:
            edge = local[a]*u(a,b)*local[b]
            gauge_product *= edge
            satisfied = satisfied and edge == 1
        assert gauge_product == -1
        assert not satisfied
    print("PASS nontrivial Z2 plaquette holonomy -1: no global nonzero parallel sign section")

if __name__ == "__main__":
    run()
