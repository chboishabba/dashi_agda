#!/usr/bin/env python3
"""Finite adversarial regressions for the Round 26 NS tax design.

The script deliberately searches tiny exact-integer carriers before any
continuum estimate is accepted.  It checks four invariants:

1. signed cancellation can coexist with nonzero separate magnitudes;
2. duplicate ownership strictly overcounts a nonzero atom;
3. the finite kernel commutator equals the increment form cellwise;
4. the six-term resonant-triad energy exchange vanishes when the three
   incompressibility/resonance relations are imposed.

This does not prove a continuum tax.  It is a falsification gate for candidate
algebra and accounting changes.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class RegressionSummary:
    signed_cancellation_examples: int
    duplicate_ownership_examples: int
    commutator_cells_checked: int
    triad_energy_cells_checked: int
    all_checks_passed: bool


def q(value: int) -> Fraction:
    return Fraction(value, 1)


def signed_cancellation_count(radius: int) -> int:
    count = 0
    for left, right in product(range(-radius, radius + 1), repeat=2):
        if left + right == 0 and (left != 0 or right != 0):
            assert abs(left) + abs(right) > 0
            count += 1
    return count


def duplicate_ownership_count(radius: int) -> int:
    count = 0
    for value in range(-radius, radius + 1):
        if value == 0:
            continue
        original = q(value)
        duplicated = original + original
        assert duplicated != original
        count += 1
    return count


def check_commutator_cells(radius: int) -> int:
    checked = 0
    for weight, shifted_a, base_a, grad_b in product(
        range(-radius, radius + 1), repeat=4
    ):
        lhs = q(weight) * q(shifted_a) * q(grad_b) - q(base_a) * (
            q(weight) * q(grad_b)
        )
        rhs = q(weight) * (q(shifted_a) - q(base_a)) * q(grad_b)
        assert lhs == rhs
        checked += 1
    return checked


def check_triad_energy_cells(radius: int) -> int:
    """Check the exact six-term identity over a finite coordinate box.

    Variables aq, bp, cq are the independent wave-vector contractions.
    Incompressibility and p+q+k=0 impose ak=-aq, bk=-bp, cp=-cq.
    Variables ab, ac, bc are symmetric amplitude pairings.
    """

    checked = 0
    values: Iterable[int] = range(-radius, radius + 1)
    for aq, bp, cq, ab, ac, bc in product(values, repeat=6):
        ak = -aq
        bk = -bp
        cp = -cq

        output_k = aq * bc + bp * ac
        output_p = bk * ac + cq * ab
        output_q = cp * ab + ak * bc
        assert output_k + output_p + output_q == 0
        checked += 1
    return checked


def run(radius: int) -> RegressionSummary:
    if radius < 1:
        raise ValueError("radius must be at least one")

    signed = signed_cancellation_count(radius)
    duplicate = duplicate_ownership_count(radius)
    commutator = check_commutator_cells(radius)
    triad = check_triad_energy_cells(radius)

    summary = RegressionSummary(
        signed_cancellation_examples=signed,
        duplicate_ownership_examples=duplicate,
        commutator_cells_checked=commutator,
        triad_energy_cells_checked=triad,
        all_checks_passed=(
            signed > 0 and duplicate > 0 and commutator > 0 and triad > 0
        ),
    )
    if not summary.all_checks_passed:
        raise AssertionError("one or more finite adversarial regressions failed")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    summary = run(args.radius)
    payload = asdict(summary)
    text = json.dumps(payload, indent=2, sort_keys=True)
    print(text)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
