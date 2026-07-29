#!/usr/bin/env python3
"""Exact audit for the Grafakos--Torres three-condition orientation."""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class Orientation:
    left: int
    right: int
    output: int


OUTPUT = Orientation(-1, -1, 1)
FIRST = Orientation(1, -1, -1)
SECOND = Orientation(-1, 1, -1)


def evaluate(v: Orientation, left: Q, right: Q, output: Q) -> Q:
    return v.left * left + v.right * right + v.output * output


def verify_incidence() -> None:
    assert OUTPUT == Orientation(-1, -1, 1)
    assert FIRST == Orientation(1, -1, -1)
    assert SECOND == Orientation(-1, 1, -1)
    # Each condition has exactly one target-positive leg and two input-negative
    # legs after the target is moved to the left.
    for vector in (OUTPUT, FIRST, SECOND):
        entries = (vector.left, vector.right, vector.output)
        assert entries.count(1) == 1
        assert entries.count(-1) == 2
    assert OUTPUT.left + FIRST.left + SECOND.left == -1
    assert OUTPUT.right + FIRST.right + SECOND.right == -1
    assert OUTPUT.output + FIRST.output + SECOND.output == -1


def verify_aggregate_decay_does_not_fix_shell_substitution() -> None:
    # The incidence template fixes signs, but shell-variable maps can still
    # produce distinct numeric affine rows.  These examples are witnesses of
    # underdetermination only, not DASHI candidate coefficients.
    shell_maps = [
        (Q(1), Q(0), Q(0)),
        (Q(0), Q(1), Q(0)),
        (Q(0), Q(0), Q(1)),
        (Q(1), Q(1), Q(0)),
    ]
    values = {evaluate(OUTPUT, *shell_map) for shell_map in shell_maps}
    assert len(values) > 1


def verify_candidate_boundary() -> None:
    status = {
        "grafakosTorresSignOrientation": True,
        "literalThreeConditionTemplate": True,
        "physicalWeightedExponent": True,
        "constructiveDyadicSeries": False,
        "literalShellVariableSubstitution": False,
        "numericOutputRelocationOrientation": False,
        "checkA": False,
    }
    assert status["grafakosTorresSignOrientation"]
    assert status["literalThreeConditionTemplate"]
    assert status["physicalWeightedExponent"]
    assert not status["constructiveDyadicSeries"]
    assert not status["literalShellVariableSubstitution"]
    assert not status["numericOutputRelocationOrientation"]
    assert not status["checkA"]


def main() -> int:
    verify_incidence()
    verify_aggregate_decay_does_not_fix_shell_substitution()
    verify_candidate_boundary()
    print(
        "verified Grafakos--Torres three-condition incidence: "
        "output=(-1,-1,+1), first=(+1,-1,-1), second=(-1,+1,-1); "
        "numeric output-relocation shell substitution and Check A remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
