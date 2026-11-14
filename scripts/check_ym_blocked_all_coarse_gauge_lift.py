#!/usr/bin/env python3
"""Exact Q8 reference for R445 selected 4D side-4 -> side-2 coarse gauge lift.

Checks ORIGINAL periodic block origin, noncommutative two-link products,
every coarse gauge generator as a pulled-back fine site gauge, and
coarse Wilson plaquette traces. Independent execution is NOT Agda
kernel acceptance, Haar integration, RG disintegration or mass gap.
"""
from itertools import product
from random import Random

UNITS = tuple(product((1, -1), range(4)))
FINE = tuple(product(range(4), repeat=4))
COARSE = tuple(product(range(2), repeat=4))
AXES = range(4)


def multiply(x, y):
    sx, ax = x
    sy, ay = y
    sign = sx * sy
    if ax == 0:
        return (sign, ay)
    if ay == 0:
        return (sign, ax)
    if ax == ay:
        return (-sign, 0)
    order = {(1, 2): 3, (2, 3): 1, (3, 1): 2}
    if (ax, ay) in order:
        return (sign, order[(ax, ay)])
    return (-sign, order[(ay, ax)])


def inverse(x):
    sign, axis = x
    return (sign if axis == 0 else -sign, axis)


def step(site, axis, modulus):
    coordinates = list(site)
    coordinates[axis] = (coordinates[axis] + 1) % modulus
    return tuple(coordinates)


def block_origin(site):
    return tuple(2 * c for c in site)


def coarse_of_fine(site):
    return tuple(c // 2 for c in site)


def blocked_links(fine):
    coarse = {}
    for site in COARSE:
        for axis in AXES:
            start = block_origin(site)
            coarse[site, axis] = multiply(
                fine[start, axis], fine[step(start, axis, 4), axis]
            )
    return coarse


def gauge_transform(links, gauge, sites, modulus):
    return {
        (site, axis): multiply(
            multiply(gauge[site], links[site, axis]),
            inverse(gauge[step(site, axis, modulus)])
        )
        for site in sites for axis in AXES
    }


def plaquette(links, site, a, b):
    sa, sb = step(site, a, 2), step(site, b, 2)
    return multiply(
        multiply(
            multiply(links[site, a], links[sa, b]),
            inverse(links[sb, a])
        ),
        inverse(links[site, b])
    )


def wilson_trace_sum(links):
    return sum(
        plaquette(links, site, a, b)[0]
        if plaquette(links, site, a, b)[1] == 0 else 0
        for site in COARSE for a in AXES for b in AXES if a < b
    )


def main():
    checks = 0
    wrong_target_detected = 0
    for site in COARSE:
        assert coarse_of_fine(block_origin(site)) == site
        checks += 1
    for seed in range(40):
        rng = Random(seed)
        fine = {(site, axis): rng.choice(UNITS)
                for site in FINE for axis in AXES}
        coarse_gauge = {site: rng.choice(UNITS) for site in COARSE}
        fine_gauge = {site: coarse_gauge[coarse_of_fine(site)]
                      for site in FINE}
        assert all(
            fine_gauge[block_origin(site)] == coarse_gauge[site]
            for site in COARSE
        )
        blocked = blocked_links(fine)
        via_fine = blocked_links(gauge_transform(fine, fine_gauge, FINE, 4))
        via_coarse = gauge_transform(blocked, coarse_gauge, COARSE, 2)
        assert via_fine == via_coarse
        assert wilson_trace_sum(blocked) == wilson_trace_sum(via_coarse)
        wrong = {
            (site, axis): multiply(
                multiply(coarse_gauge[site], blocked[site, axis]),
                coarse_gauge[step(site, axis, 2)]
            )
            for site in COARSE for axis in AXES
        }
        wrong_target_detected += (wrong != via_fine)
        checks += len(COARSE) + 64 + 1
    assert wrong_target_detected > 0
    print("PASS: exact Q8 side4->side2 gauge lift; "
          f"{checks} origin, lift, link and Wilson checks; "
          f"{wrong_target_detected}/40 bad-target-inverse controls rejected")
    print("REFERENCE ONLY: not Agda, continuous SU(N) Haar, RG or Clay.")


if __name__ == "__main__":
    main()
