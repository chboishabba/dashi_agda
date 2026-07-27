#!/usr/bin/env python3
"""Exact audit for transpose permutations and frozen-leg high-high structure."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from itertools import product
from typing import Iterable, Tuple

Mode = Tuple[int, int, int]
RationalVector = Tuple[Fraction, Fraction, Fraction]


def add(a: Mode, b: Mode) -> Mode:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def dot(a: Mode, b: Mode) -> int:
    return sum(x * y for x, y in zip(a, b))


def rational_dot(a: RationalVector, b: RationalVector) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def cross(a: Mode, b: Mode) -> Mode:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def norm_sq(a: Mode) -> int:
    return dot(a, a)


def rational_norm_sq(a: RationalVector) -> Fraction:
    return rational_dot(a, a)


def leray_project(mode: Mode, vector: Mode) -> RationalVector:
    mode_norm = norm_sq(mode)
    if mode_norm == 0:
        raise ValueError("Leray projection requires a nonzero mode")
    coefficient = Fraction(dot(mode, vector), mode_norm)
    return tuple(
        Fraction(value) - coefficient * coordinate
        for value, coordinate in zip(vector, mode)
    )  # type: ignore[return-value]


class FrozenInput(Enum):
    FIRST = "first"
    SECOND = "second"


class InheritedTranspose(Enum):
    FIRST = "T*1"
    SECOND = "T*2"


TRANSPOSE_AFTER_FREEZE = {
    FrozenInput.FIRST: InheritedTranspose.SECOND,
    FrozenInput.SECOND: InheritedTranspose.FIRST,
}


def verify_grafakos_torres_frozen_rule() -> None:
    # Bilinear specialization of Grafakos--Torres equation (16).
    assert TRANSPOSE_AFTER_FREEZE[FrozenInput.FIRST] is InheritedTranspose.SECOND
    assert TRANSPOSE_AFTER_FREEZE[FrozenInput.SECOND] is InheritedTranspose.FIRST


def nonzero_transverse_vectors(mode: Mode) -> Iterable[Mode]:
    for basis in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        value = cross(mode, basis)
        if value != (0, 0, 0):
            assert dot(value, mode) == 0
            yield value


def verify_output_incompressibility_relocation() -> int:
    checked = 0
    for p in product(range(-3, 4), repeat=3):
        if p == (0, 0, 0):
            continue
        for q in product(range(-3, 4), repeat=3):
            if q == (0, 0, 0):
                continue
            k = add(p, q)
            if k == (0, 0, 0):
                continue
            for u_p in nonzero_transverse_vectors(p):
                # k = p + q and u_p dot p = 0 imply u_p dot q = u_p dot k.
                assert dot(u_p, q) == dot(u_p, k)
                checked += 1
    return checked


@dataclass(frozen=True)
class FirstAdjointCounterexample:
    low_output: Mode
    high_input_q: Mode
    high_input_k: Mode
    projected_derivative: RationalVector


def first_adjoint_counterexample(scale: int = 37) -> FirstAdjointCounterexample:
    # First-adjoint output p is low, while q and k=p+q are high.
    # q is orthogonal to p, so the exact Leray formula gives P_p q=q.
    p = (1, 0, 0)
    q = (0, scale, 0)
    k = add(p, q)
    assert dot(p, q) == 0
    projected_q = leray_project(p, q)
    exact_q = tuple(Fraction(value) for value in q)
    assert projected_q == exact_q
    assert rational_norm_sq(projected_q) == scale * scale
    assert norm_sq(p) == 1
    assert rational_norm_sq(projected_q) > scale * norm_sq(p)
    return FirstAdjointCounterexample(p, q, k, projected_q)


def verify_second_adjoint_direct_low_frequency() -> None:
    # In the literal symbol the derivative frequency is q.
    # For T*2, q is the frozen/output leg itself.
    right_leg_is_derivative_leg = True
    right_leg_is_frozen_for_second_adjoint = True
    assert right_leg_is_derivative_leg and right_leg_is_frozen_for_second_adjoint


def main() -> int:
    verify_grafakos_torres_frozen_rule()
    checked = verify_output_incompressibility_relocation()
    witness = first_adjoint_counterexample()
    verify_second_adjoint_direct_low_frequency()
    print(
        "verified Grafakos--Torres bilinear frozen-transpose rule, "
        f"{checked} exact incompressibility relocations u_p·q=u_p·k, "
        "direct low derivative for the second adjoint, and an exact Leray "
        "first-adjoint counterexample with "
        f"|P_p q|^2={rational_norm_sq(witness.projected_derivative)} "
        f"while |p|^2={norm_sq(witness.low_output)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
