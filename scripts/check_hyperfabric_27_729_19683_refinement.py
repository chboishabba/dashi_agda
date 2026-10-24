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
    print("BOUNDARY free graph operators only; selected physical gauge/GR/string/YM/NS remains unpaid")


if __name__ == "__main__":
    run()
