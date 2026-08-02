#!/usr/bin/env python3
"""Exact rational audit for the ordered-l2 and hard-shell Stage-3 tranche."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import random

Vec3 = tuple[Fraction, Fraction, Fraction]
Mode = tuple[int, int, int]


def dot(a: Vec3, b: Vec3) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def sub(a: Vec3, b: Vec3) -> Vec3:
    return tuple(x - y for x, y in zip(a, b))  # type: ignore[return-value]


def scale(c: Fraction, a: Vec3) -> Vec3:
    return tuple(c * x for x in a)  # type: ignore[return-value]


def norm2(a: Vec3) -> Fraction:
    return dot(a, a)


def leray(p: Vec3, q: Vec3) -> Vec3:
    p2 = norm2(p)
    if p2 == 0:
        raise ValueError("Leray mode must be nonzero")
    return sub(q, scale(dot(p, q) / p2, p))


def verify_leray() -> int:
    checked = 0
    for p_int in product(range(-4, 5), repeat=3):
        if p_int == (0, 0, 0):
            continue
        p = tuple(Fraction(x) for x in p_int)
        for q_int in product(range(-3, 4), repeat=3):
            q = tuple(Fraction(x) for x in q_int)
            projected = leray(p, q)
            correction = dot(p, q) ** 2 / norm2(p)
            assert norm2(projected) == norm2(q) - correction
            assert norm2(projected) <= norm2(q)
            assert dot(p, projected) == 0
            checked += 1
    return checked


def verify_transverse_uniqueness() -> int:
    rng = random.Random(369031)
    for _ in range(4000):
        p_raw = [rng.randint(-6, 6) for _ in range(3)]
        if p_raw == [0, 0, 0]:
            p_raw[0] = 1
        p = tuple(Fraction(x) for x in p_raw)
        u0 = tuple(Fraction(rng.randint(-8, 8), rng.randint(1, 7)) for _ in range(3))
        v0 = tuple(Fraction(rng.randint(-8, 8), rng.randint(1, 7)) for _ in range(3))
        u, v = leray(p, u0), leray(p, v0)
        difference = sub(u, v)
        assert dot(p, difference) == 0
        same_difference_test = dot(difference, u) == dot(difference, v)
        assert same_difference_test == (norm2(difference) == 0)
        if same_difference_test:
            assert u == v
    return 4000


def mode_add(a: Mode, b: Mode) -> Mode:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def mode_norm2(k: Mode) -> int:
    return sum(coordinate * coordinate for coordinate in k)


def shell_index(k: Mode) -> int | None:
    radius2 = mode_norm2(k)
    if radius2 == 0:
        return None
    shell, lower = 0, 1
    while not lower <= radius2 < 4 * lower:
        shell, lower = shell + 1, 4 * lower
    return shell


def geometry(j_left: int, j_right: int, j_output: int) -> str:
    if j_left + 3 <= j_right and j_left + 3 <= j_output:
        return "left-low"
    if j_right + 3 <= j_left and j_right + 3 <= j_output:
        return "right-low"
    if j_output + 3 <= j_left and j_output + 3 <= j_right:
        return "output-low"
    span = max(j_left, j_right, j_output) - min(j_left, j_right, j_output)
    if span <= 1:
        return "comparable"
    if span == 2:
        return "transition"
    return "residual"


def verify_geometry() -> tuple[int, dict[str, int]]:
    tags = ("left-low", "right-low", "output-low", "comparable", "transition", "residual")
    counts = {tag: 0 for tag in tags}
    for triple in product(range(10), repeat=3):
        tag = geometry(*triple)
        counts[tag] += 1
        separated = (
            triple[0] + 3 <= triple[1] and triple[0] + 3 <= triple[2],
            triple[1] + 3 <= triple[0] and triple[1] + 3 <= triple[2],
            triple[2] + 3 <= triple[0] and triple[2] + 3 <= triple[1],
        )
        assert sum(separated) <= 1
    return 1000, counts


ARCHETYPES = {
    ("output", "unsplit", "left-low"): ("low-high", 5, 3),
    ("output", "unsplit", "right-low"): ("low-low", 5, 5),
    ("output", "unsplit", "output-low"): ("output-relocation", 5, 10),
    ("first", "direct", "left-low"): ("first-convolution", 5, 8),
    ("first", "direct", "right-low"): ("low-low", 5, 5),
    ("first", "direct", "output-low"): ("low-high", 5, 3),
    ("first", "swapped", "left-low"): ("second-frozen", 5, 10),
    ("first", "swapped", "right-low"): ("low-high", 5, 3),
    ("first", "swapped", "output-low"): ("low-high", 5, 3),
    ("second", "unsplit", "left-low"): ("low-high", 5, 3),
    ("second", "unsplit", "right-low"): ("second-frozen", 5, 10),
    ("second", "unsplit", "output-low"): ("low-high", 5, 3),
}


def verify_component_table() -> int:
    assert len(ARCHETYPES) == 12
    assert {entry[0] for entry in ARCHETYPES.values()} == {
        "low-high", "low-low", "first-convolution", "output-relocation", "second-frozen"
    }
    assert all(low == 5 and gap > 0 for _, low, gap in ARCHETYPES.values())
    return len(ARCHETYPES)


def shell_modes(shell: int, cutoff: int) -> list[Mode]:
    return [
        mode
        for mode in product(range(-cutoff, cutoff + 1), repeat=3)
        if shell_index(mode) == shell
    ]


def convolution_at(output: Mode, left: dict[Mode, Fraction], right: dict[Mode, Fraction]) -> Fraction:
    return sum(
        (coefficient * right.get(mode_add(output, source), Fraction(0))
         for source, coefficient in left.items()),
        Fraction(0),
    )


def l2_squared(values: dict[Mode, Fraction]) -> Fraction:
    return sum((value * value for value in values.values()), Fraction(0))


def verify_convolution() -> int:
    rng, checked = random.Random(143922), 0
    for cutoff in range(2, 8):
        universe = list(product(range(-cutoff, cutoff + 1), repeat=3))
        for low_shell in range(3):
            outputs = shell_modes(low_shell, cutoff)
            if not outputs:
                continue
            for _ in range(80):
                left_keys = rng.sample(universe, min(len(universe), rng.randint(1, 18)))
                right_keys = rng.sample(universe, min(len(universe), rng.randint(1, 18)))
                left = {key: Fraction(rng.randint(-7, 7), rng.randint(1, 5)) for key in left_keys}
                right = {key: Fraction(rng.randint(-7, 7), rng.randint(1, 5)) for key in right_keys}
                output_norm = sum((convolution_at(p, left, right) ** 2 for p in outputs), Fraction(0))
                assert output_norm <= Fraction(len(outputs)) * l2_squared(left) * l2_squared(right)
                checked += 1
    return checked


def verify_shell_count() -> int:
    for shell in range(20):
        coordinate_count = 2 ** (shell + 2) - 1
        assert coordinate_count**3 <= 125 * 2 ** (3 * shell)
    for shell in range(5):
        exact_count = len(shell_modes(shell, 2 ** (shell + 1)))
        assert exact_count <= 125 * 2 ** (3 * shell)
    return 25


def verify_gap_three() -> int:
    checked = 0
    for low in range(8):
        for high in range(low + 3, 12):
            assert Fraction(2 ** (low + 1), 2**high) <= Fraction(1, 4)
            checked += 1
    return checked


def main() -> int:
    leray_cases = verify_leray()
    uniqueness_cases = verify_transverse_uniqueness()
    geometry_cases, geometry_counts = verify_geometry()
    component_rows = verify_component_table()
    convolution_cases = verify_convolution()
    shell_count_cases = verify_shell_count()
    gap_cases = verify_gap_three()

    assert 125 * (48 * 8 * 2) ** 2 == 73_728_000
    assert (2 * 1 + 1) ** 2 == 9
    assert 2 * (2 + 1) == 6
    assert component_rows == 12

    proved_uniform_archetype_count = 0
    assert proved_uniform_archetype_count < 5

    print(
        "ordered-l2/shell audit passed: "
        f"{leray_cases} Leray cases, {uniqueness_cases} transverse cases, "
        f"{geometry_cases} geometry triples {geometry_counts}, "
        f"{component_rows} separated components, {convolution_cases} convolution cases, "
        f"{shell_count_cases} shell-count checks, {gap_cases} gap-three checks"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
