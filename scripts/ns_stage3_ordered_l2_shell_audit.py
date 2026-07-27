#!/usr/bin/env python3
"""Exact rational audit for the ordered-l2 and hard-shell Stage-3 tranche."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import random

Vec3 = tuple[Fraction, Fraction, Fraction]
CVec3 = tuple[complex, complex, complex]
Mode = tuple[int, int, int]


def dot(a: Vec3, b: Vec3) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def add(a: Vec3, b: Vec3) -> Vec3:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


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
    values = range(-4, 5)
    for p_int in product(values, repeat=3):
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
    checked = 0
    rng = random.Random(369031)
    for _ in range(4000):
        p_int = [rng.randint(-6, 6) for _ in range(3)]
        if p_int == [0, 0, 0]:
            p_int[0] = 1
        p = tuple(Fraction(x) for x in p_int)
        u0 = tuple(Fraction(rng.randint(-8, 8), rng.randint(1, 7)) for _ in range(3))
        v0 = tuple(Fraction(rng.randint(-8, 8), rng.randint(1, 7)) for _ in range(3))
        u = leray(p, u0)
        v = leray(p, v0)
        d = sub(u, v)
        assert dot(p, u) == 0 and dot(p, v) == 0 and dot(p, d) == 0
        same_self_test = dot(d, u) == dot(d, v)
        assert same_self_test == (norm2(d) == 0)
        if same_self_test:
            assert u == v
        checked += 1
    return checked


def mode_add(a: Mode, b: Mode) -> Mode:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def mode_norm2(k: Mode) -> int:
    return k[0] * k[0] + k[1] * k[1] + k[2] * k[2]


def shell_index(k: Mode) -> int | None:
    radius2 = mode_norm2(k)
    if radius2 == 0:
        return None
    j = 0
    lower = 1
    while not (lower <= radius2 < 4 * lower):
        lower *= 4
        j += 1
    return j


def geometry(jl: int, jr: int, jo: int) -> str:
    if jl + 3 <= jr and jl + 3 <= jo:
        return "left-low"
    if jr + 3 <= jl and jr + 3 <= jo:
        return "right-low"
    if jo + 3 <= jl and jo + 3 <= jr:
        return "output-low"
    span = max(jl, jr, jo) - min(jl, jr, jo)
    if span <= 1:
        return "comparable"
    if span == 2:
        return "transition"
    return "residual"


def verify_geometry() -> tuple[int, dict[str, int]]:
    counts: dict[str, int] = {
        "left-low": 0,
        "right-low": 0,
        "output-low": 0,
        "comparable": 0,
        "transition": 0,
        "residual": 0,
    }
    checked = 0
    for jl, jr, jo in product(range(10), repeat=3):
        tag = geometry(jl, jr, jo)
        counts[tag] += 1
        checked += 1
        separated = [
            jl + 3 <= jr and jl + 3 <= jo,
            jr + 3 <= jl and jr + 3 <= jo,
            jo + 3 <= jl and jo + 3 <= jr,
        ]
        assert sum(separated) <= 1
        if tag == "comparable":
            assert max(jl, jr, jo) - min(jl, jr, jo) <= 1
        if tag == "transition":
            assert max(jl, jr, jo) - min(jl, jr, jo) == 2
    return checked, counts


ARCHETYPES: dict[tuple[str, str, str], str] = {
    ("output", "unsplit", "left-low"): "low-Bernstein-derivative-high",
    ("output", "unsplit", "right-low"): "low-Bernstein-derivative-low",
    ("output", "unsplit", "output-low"): "output-relocation",
    ("first", "direct", "left-low"): "high-high-first-adjoint-convolution",
    ("first", "direct", "right-low"): "low-Bernstein-derivative-low",
    ("first", "direct", "output-low"): "low-Bernstein-derivative-high",
    ("first", "swapped", "left-low"): "high-high-first-adjoint-convolution",
    ("first", "swapped", "right-low"): "low-Bernstein-derivative-low",
    ("first", "swapped", "output-low"): "low-Bernstein-derivative-high",
    ("second", "unsplit", "left-low"): "low-Bernstein-derivative-high",
    ("second", "unsplit", "right-low"): "second-frozen-low-derivative",
    ("second", "unsplit", "output-low"): "low-Bernstein-derivative-high",
}


def verify_component_table() -> int:
    assert len(ARCHETYPES) == 12
    assert set(ARCHETYPES.values()) == {
        "low-Bernstein-derivative-high",
        "low-Bernstein-derivative-low",
        "high-high-first-adjoint-convolution",
        "output-relocation",
        "second-frozen-low-derivative",
    }
    return len(ARCHETYPES)


def shell_modes(shell: int, cutoff: int) -> list[Mode]:
    result: list[Mode] = []
    for mode in product(range(-cutoff, cutoff + 1), repeat=3):
        if shell_index(mode) == shell:
            result.append(mode)
    return result


def convolution_at(
    output: Mode,
    left: dict[Mode, Fraction],
    right: dict[Mode, Fraction],
) -> Fraction:
    total = Fraction(0)
    for q, aq in left.items():
        total += aq * right.get(mode_add(output, q), Fraction(0))
    return total


def l2_squared(values: dict[Mode, Fraction]) -> Fraction:
    return sum((value * value for value in values.values()), Fraction(0))


def verify_convolution() -> int:
    rng = random.Random(143922)
    checked = 0
    for cutoff in range(2, 8):
        universe = list(product(range(-cutoff, cutoff + 1), repeat=3))
        for low_shell in range(0, 3):
            outputs = shell_modes(low_shell, cutoff)
            if not outputs:
                continue
            for _ in range(80):
                left_support = rng.sample(universe, min(len(universe), rng.randint(1, 18)))
                right_support = rng.sample(universe, min(len(universe), rng.randint(1, 18)))
                left = {k: Fraction(rng.randint(-7, 7), rng.randint(1, 5)) for k in left_support}
                right = {k: Fraction(rng.randint(-7, 7), rng.randint(1, 5)) for k in right_support}
                output_norm = sum(
                    (convolution_at(p, left, right) ** 2 for p in outputs),
                    Fraction(0),
                )
                rhs = Fraction(len(outputs)) * l2_squared(left) * l2_squared(right)
                assert output_norm <= rhs
                checked += 1
    return checked


def verify_shell_count() -> int:
    checked = 0
    for shell in range(7):
        cutoff = 2 ** (shell + 2)
        count = len(shell_modes(shell, cutoff))
        assert count <= 125 * (2 ** (3 * shell))
        checked += 1
    return checked


def verify_gap_three() -> int:
    checked = 0
    for low in range(8):
        for high in range(low + 3, 12):
            low_upper = Fraction(2 ** (low + 1))
            high_lower = Fraction(2**high)
            assert low_upper / high_lower <= Fraction(1, 4)
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

    # A strict affine certificate is intentionally unavailable until every
    # component has a proved numeric analytic inequality, not merely a mapped
    # archetype.
    proved_numeric_component_count = 2
    assert proved_numeric_component_count < component_rows

    print(
        "ordered-l2/shell audit passed: "
        f"{leray_cases} Leray cases, "
        f"{uniqueness_cases} transverse uniqueness cases, "
        f"{geometry_cases} geometry triples {geometry_counts}, "
        f"{component_rows} separated components, "
        f"{convolution_cases} convolution cases, "
        f"{shell_count_cases} shell counts, {gap_cases} gap-three cases"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
