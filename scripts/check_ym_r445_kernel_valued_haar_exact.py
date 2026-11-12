#!/usr/bin/env python3
"""Exact noncommutative regression for original one-pair kernel-valued Haar transport.

D4 is an independent finite control, not SU(N), an Agda receipt, or a
physical Wilson RG estimate. The kernel and fine density are allowed to
be signed and to depend jointly on every link coordinate.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random

GROUP = tuple((r, s) for s in (0, 1) for r in range(4))


def mul(a, b):
    return ((a[0] + (-1 if a[1] else 1) * b[0]) % 4, (a[1] + b[1]) % 2)


def inv(a):
    r, s = a
    return ((-r if s == 0 else r) % 4, s)


def mean(seq):
    return sum(seq, Q(0)) / len(GROUP)


def check_kernel(rng):
    kernel = {(u, v, w): Q(rng.randrange(-13, 14), rng.randrange(1, 9))
              for u, v, w in product(GROUP, repeat=3)}
    left = mean(mean(kernel[u, v, mul(u, v)] for v in GROUP) for u in GROUP)
    right = mean(mean(kernel[u, mul(inv(u), w), w] for u in GROUP) for w in GROUP)
    assert left == right, (left, right)


def check_all_interior(rng):
    interior = tuple(product(GROUP, repeat=2))
    density = {(u, v, i): Q(rng.randrange(-13, 14), rng.randrange(1, 9))
               for u in GROUP for v in GROUP for i in interior}
    observable = {w: Q(rng.randrange(-13, 14), rng.randrange(1, 7)) for w in GROUP}

    def interior_integral(u, v, w):
        return sum((density[u, v, i] * observable[w] for i in interior), Q(0)) / len(interior)

    left = mean(mean(interior_integral(u, v, mul(u, v)) for v in GROUP) for u in GROUP)
    right = mean(mean(interior_integral(u, mul(inv(u), w), w) for u in GROUP) for w in GROUP)
    assert left == right, (left, right)


def main():
    rng = Random(14441498)
    for u in GROUP:
        for v in GROUP:
            assert mul(inv(u), mul(u, v)) == v
            assert mul(u, mul(inv(u), v)) == v
    for _ in range(256):
        check_kernel(rng)
    for _ in range(32):
        check_all_interior(rng)
    print("PASS 256 arbitrary signed D4 kernel change-of-variable instances")
    print("PASS 32 fully coupled signed D4 density + two-interior-link instances")
    print("BOUNDARY: no Agda kernel / SU(N) Haar / Wilson RG or mass gap receipt")


if __name__ == "__main__":
    main()
