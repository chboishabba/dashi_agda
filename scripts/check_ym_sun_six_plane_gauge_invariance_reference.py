#!/usr/bin/env python3
"""Independent finite numerical check for original six-plane SU(2) link gauge law.

This is NOT Agda kernel verification and NOT compact SU(2) Haar,
UV limit, or mass-gap evidence. It tests source-level orientation
and gauge-transform conventions on a nonconstant 4D side-four torus.

Original mathematical sources: K. Wilson, Phys. Rev. D 10 (1974),
DOI: 10.1103/PhysRevD.10.2445; T. Balaban, CMP 99 (1985),
DOI: 10.1007/BF01466594. Reference Python fixture: DASHI extension.
"""
from itertools import product

import numpy as np

SIDE = 4
SEED = 20261102
SITES = list(product(range(SIDE), repeat=4))
PLANES = [(a, b) for a in range(4) for b in range(a + 1, 4)]


def mul(q, r):
    a, b, c, d = q
    e, f, g, h = r
    return np.array(
        [a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
         a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e],
        dtype=float,
    )


def inverse(q):
    return q * np.array([1.0, -1.0, -1.0, -1.0])


def step(site, axis):
    return tuple((x + 1) % SIDE if i == axis else x
                 for i, x in enumerate(site))


def plaquette(links, site, a, b):
    """Native signed word (+a,+b,-a,-b), original six a<b planes."""
    return mul(
        mul(
            mul(links[site, a], links[step(site, a), b]),
            inverse(links[step(site, b), a]),
        ),
        inverse(links[site, b]),
    )


def action(links):
    return sum(1.0 - plaquette(links, site, a, b)[0]
               for site in SITES for a, b in PLANES)


def main():
    rng = np.random.default_rng(SEED)

    def unit():
        x = rng.normal(size=4)
        return x / np.linalg.norm(x)

    links = {(site, axis): unit() for site in SITES for axis in range(4)}
    gauge = {site: unit() for site in SITES}
    transformed = {
        (site, axis): mul(
            mul(gauge[site], links[site, axis]),
            inverse(gauge[step(site, axis)]),
        )
        for site in SITES for axis in range(4)
    }
    maximum = max(
        abs(plaquette(links, site, a, b)[0] -
            plaquette(transformed, site, a, b)[0])
        for site in SITES for a, b in PLANES
    )
    original = action(links)
    gauged = action(transformed)
    assert maximum < 1e-12
    assert abs(original - gauged) < 1e-9
    print({
        "sites": len(SITES),
        "positive_links": len(links),
        "original_six_plane_plaquettes": len(SITES)*len(PLANES),
        "max_trace_gauge_error": maximum,
        "six_action": original,
        "gauge_action": gauged,
        "abs_action_error": abs(original - gauged),
        "status": "PASS (finite numerical reference only)",
    })


if __name__ == "__main__":
    main()


# Variable-periodic (suc n) regression for the R443/R445 original SU(2)
# six-positive-plane gauge convention. Reuses mul/inverse from the original
# side-four reference instead of constructing another algebra.
# Different side lengths are distinct finite lattices. This does NOT check
# any Haar integral, cylinder refinement, continuum limit or Agda kernel.
def check_variable_periodic_side(side, seed):
    rng = np.random.default_rng(seed)
    sites = list(product(range(side), repeat=4))

    def unit_quaternion():
        q = rng.normal(size=4)
        return q / np.linalg.norm(q)

    def step_variable(site, axis):
        return tuple((coordinate + 1) % side if i == axis else coordinate
                     for i, coordinate in enumerate(site))

    def plaquette_variable(links, site, a, b):
        return mul(
            mul(
                mul(links[site, a], links[step_variable(site, a), b]),
                inverse(links[step_variable(site, b), a]),
            ),
            inverse(links[site, b]),
        )

    links = {(site, axis): unit_quaternion()
             for site in sites for axis in range(4)}
    gauge = {site: unit_quaternion() for site in sites}
    correct = {
        (site, axis): mul(
            mul(gauge[site], links[site, axis]),
            inverse(gauge[step_variable(site, axis)]),
        )
        for site in sites for axis in range(4)
    }
    wrong_right_orientation = {
        (site, axis): mul(
            mul(gauge[site], links[site, axis]),
            gauge[step_variable(site, axis)],
        )
        for site in sites for axis in range(4)
    }

    def compare(transformed):
        deviations = [
            abs(plaquette_variable(links, site, a, b)[0] -
                plaquette_variable(transformed, site, a, b)[0])
            for site in sites for a, b in PLANES
        ]
        return max(deviations), sum(deviations)

    max_err, sum_err = compare(correct)
    wrong_max, _ = compare(wrong_right_orientation)
    assert len(sites) == side**4
    assert len(links) == 4 * side**4
    assert max_err < 1e-12, (side, max_err)
    assert sum_err < 1e-8, (side, sum_err)
    # A deliberately incorrect target-gauge orientation must be rejected.
    assert wrong_max > 1e-4, (side, wrong_max)
    return {
        "side": side,
        "sites": len(sites),
        "positive_links": len(links),
        "plaquettes_checked": 6 * len(sites),
        "max_trace_error": max_err,
        "sum_trace_error": sum_err,
        "wrong_inverse_max_error": wrong_max,
        "status": "PASS (finite numerical gauge regression only)",
    }


if __name__ == "__main__":
    for variable_side in (2, 3, 5):
        print(check_variable_periodic_side(
            variable_side, SEED + variable_side))
