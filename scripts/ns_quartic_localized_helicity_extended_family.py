#!/usr/bin/env python3
"""Extend localized-helicity reconnaissance across symmetries and perturbations."""
from __future__ import annotations

from fractions import Fraction as F
from itertools import permutations, product

import ns_quartic_localized_helicity_reconnaissance as base


def signed_permutations():
    return list(product(permutations(range(3)), product((-1, 1), repeat=3)))


def transform_mode(mode, transform, scale=1):
    permutation, signs = transform
    return tuple(scale * signs[i] * mode[permutation[i]] for i in range(3))


def transform_vector(value, transform):
    permutation, signs = transform
    return [base.cs(F(signs[i]), value[permutation[i]]) for i in range(3)]


def transform_state(state, transform, scale=1):
    return {
        transform_mode(mode, transform, scale): transform_vector(value, transform)
        for mode, value in state.items()
    }


def merge_states(*states):
    merged = {}
    for state in states:
        assert not set(merged).intersection(state)
        merged.update(state)
    return merged


def transverse_perturbation(state, coefficient):
    return {
        mode: base.va(
            value,
            [base.cs(coefficient, entry) for entry in base.curl(mode, value)],
        )
        for mode, value in state.items()
    }


def main() -> int:
    witness = base.state()
    a0, b0, c0, localized0 = base.metrics(witness)
    gap0 = c0 * c0 - 4 * a0 * b0
    assert gap0 == F(28_984_957_666_432)
    assert not any(localized0.values())

    transforms = signed_permutations()
    assert len(transforms) == 48
    distinct_supports = set()
    for transform in transforms:
        rotated = transform_state(witness, transform)
        distinct_supports.add(tuple(sorted(rotated)))
        a, b, cubic, localized = base.metrics(rotated)
        assert (a, b, cubic, cubic * cubic - 4 * a * b) == (
            a0,
            b0,
            c0,
            gap0,
        )
        assert not any(localized.values())
    assert len(distinct_supports) == 12

    for scale in (2, 3, 4, 5):
        dilated = transform_state(witness, transforms[0], scale)
        a, b, cubic, localized = base.metrics(dilated)
        assert cubic * cubic - 4 * a * b > 0
        assert not any(localized.values())

    cluster_scales = ((1, 2), (1, 3), (1, 4), (2, 4), (1, 2, 4))
    for scales in cluster_scales:
        cluster = merge_states(
            *(transform_state(witness, transforms[0], scale) for scale in scales)
        )
        a, b, cubic, localized = base.metrics(cluster)
        assert cubic * cubic - 4 * a * b > 0
        assert not any(localized.values())

    attempts = 0
    repairs = 0
    perturbations = (
        F(1, 100),
        F(-1, 100),
        F(1, 20),
        F(-1, 20),
        F(1, 10),
        F(-1, 10),
    )
    for coefficient in perturbations:
        perturbed = transverse_perturbation(witness, coefficient)
        a, b, cubic, localized = base.metrics(perturbed)
        assert cubic * cubic - 4 * a * b > 0
        assert any(localized.values())
        best_gap = None
        for _, symbol in base.symbols():
            correction = sum(
                symbol(base.n2(mode)) * value
                for mode, value in localized.items()
            )
            for sign, epsilon in product((-1, 1), range(8)):
                attempts += 1
                gap = (cubic + sign * epsilon * correction) ** 2 - 4 * a * b
                if best_gap is None or gap < best_gap:
                    best_gap = gap
                if gap <= 0:
                    repairs += 1
        assert best_gap is not None and best_gap > 0

    assert attempts == 2688
    assert repairs == 0
    print(
        "verified extended localized-helicity family: 48 signed lattice "
        "symmetries (12 distinct supports), 4 support dilations, 5 larger "
        "balanced clusters, and 6 transverse perturbations across 2,688 "
        "symbol/sign/epsilon attempts; no repair found"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
