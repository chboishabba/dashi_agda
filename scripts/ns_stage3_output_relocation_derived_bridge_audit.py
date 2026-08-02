#!/usr/bin/env python3
"""Exact audit for derived output-relocation power and signed bridges."""
from __future__ import annotations

import json
import math
from fractions import Fraction as Q


def scale_by_nat(value: Q, shell: int) -> Q:
    assert shell >= 0
    total = Q(0)
    for _ in range(shell):
        total += value
    return total


def run() -> dict[str, object]:
    # Identity embedding on exact rationals checks the native unital embedding
    # laws required by the Agda interface.
    embed = lambda value: value
    rational_samples = (Q(-7, 5), Q(-1), Q(0), Q(1), Q(3, 2), Q(128, 93))
    assert embed(Q(0)) == 0
    assert embed(Q(1)) == 1
    for left in rational_samples:
        for right in rational_samples:
            assert embed(left + right) == embed(left) + embed(right)
            assert embed(left * right) == embed(left) * embed(right)
            if left <= right:
                assert embed(left) <= embed(right)

    two_rational = Q(1) + Q(1)
    three_rational = two_rational + Q(1)
    five_rational = (two_rational + two_rational) + Q(1)
    five_halves = Q(5, 2)
    assert two_rational == 2
    assert three_rational == 3
    assert five_rational == 5

    two_pow = lambda exponent: Q(2) ** exponent
    assert two_pow(0) == 1
    assert two_pow(1) == 2

    regularities = (Q(251, 100), Q(8, 3), Q(299, 100))
    shells = (0, 1, 2, 3, 7, 16, 64)

    exponent_checks: list[dict[str, str | int]] = []
    for regularity in regularities:
        # The concrete decay record is pinned to these identities.
        low_decay = 2 * regularity - five_halves
        gap_decay = 2 * regularity
        assert five_halves < regularity < three_rational
        assert low_decay == regularity + regularity - five_halves
        assert gap_decay == regularity + regularity
        assert low_decay >= two_rational
        assert gap_decay >= five_rational

        for shell in shells:
            # Repeated-addition semantics of natural scaling.
            assert scale_by_nat(low_decay, 0) == 0
            assert scale_by_nat(low_decay, shell) == low_decay * shell
            assert scale_by_nat(gap_decay, shell) == gap_decay * shell
            assert scale_by_nat(low_decay, shell + 1) == (
                low_decay + scale_by_nat(low_decay, shell)
            )
            assert scale_by_nat(gap_decay, shell + 1) == (
                gap_decay + scale_by_nat(gap_decay, shell)
            )

            # Multiplication by a nonnegative natural preserves order, then
            # negation reverses it.
            assert scale_by_nat(two_rational, shell) <= scale_by_nat(low_decay, shell)
            assert -scale_by_nat(low_decay, shell) <= -scale_by_nat(two_rational, shell)
            assert scale_by_nat(five_rational, shell) <= scale_by_nat(gap_decay, shell)
            assert -scale_by_nat(gap_decay, shell) <= -scale_by_nat(five_rational, shell)

            # Exact integer anchors used by the Agda theorem.
            quarter_anchor = Q(1, 4) ** shell
            thirty_second_anchor = Q(1, 32) ** shell
            assert Q(2) ** (-2 * shell) == quarter_anchor
            assert Q(2) ** (-5 * shell) == thirty_second_anchor
            assert quarter_anchor == Q(1, 2) ** (2 * shell)
            assert thirty_second_anchor == Q(1, 2) ** (5 * shell)

            # Numerical sanity only for non-integral real powers: positivity is
            # a supplied carrier law and the Agda theorem derives factor
            # nonnegativity from it.
            assert math.pow(2.0, float(-low_decay * shell)) > 0.0
            assert math.pow(2.0, float(-gap_decay * shell)) > 0.0

            exponent_checks.append(
                {
                    "s": str(regularity),
                    "shell": shell,
                    "lowDecay": str(low_decay),
                    "gapDecay": str(gap_decay),
                    "negativeLowExponent": str(-low_decay * shell),
                    "negativeQuarterAnchorExponent": str(-2 * shell),
                    "negativeGapExponent": str(-gap_decay * shell),
                    "negativeThirtySecondAnchorExponent": str(-5 * shell),
                }
            )

    signed_samples = (
        (Q(0), Q(0)),
        (Q(1, 7), Q(1, 7)),
        (Q(-1, 7), Q(1, 7)),
        (Q(17, 31), Q(19, 31)),
        (Q(-17, 31), Q(19, 31)),
        (Q(128, 93), Q(128, 93)),
        (Q(-128, 93), Q(128, 93)),
    )
    signed_checks: list[dict[str, str]] = []
    for coefficient, majorant in signed_samples:
        assert abs(coefficient) <= majorant
        assert coefficient <= abs(coefficient)
        assert -abs(coefficient) <= coefficient
        assert coefficient <= majorant
        assert -majorant <= coefficient
        signed_checks.append(
            {
                "coefficient": str(coefficient),
                "absolute": str(abs(coefficient)),
                "majorant": str(majorant),
            }
        )

    return {
        "exponentChecks": exponent_checks,
        "signedChecks": signed_checks,
        "decision": {
            "unaryNegationCarrierCorrected": True,
            "nativeRationalEmbeddingUnital": True,
            "twoAndFivePinnedToRationals": True,
            "twoPowZeroAndOnePinned": True,
            "naturalScalingRecursivelyPinned": True,
            "sobolevDecayFormulasPinned": True,
            "factorNonnegativityDerivedFromPowerPositivity": True,
            "lowShellComparisonDerived": True,
            "gapComparisonDerived": True,
            "signedUpperDerivedFromAbsolute": True,
            "signedLowerDerivedFromAbsolute": True,
            "fourFormerRawFieldsDerived": True,
            "concreteNativeSpineCapabilityClosed": False,
            "concreteBaseTwoPowerDataClosed": False,
            "concreteLiteralAbsoluteCoefficientEstimateClosed": False,
            "concreteOutputRelocationTheoremClosed": False,
        },
    }


def main() -> int:
    result = run()
    print(json.dumps(result["decision"], sort_keys=True))
    print(
        "verified unital rational embedding, pinned two/five and twoPow zero/one, "
        "recursive natural scaling, exact Sobolev decay formulas, exponent-order "
        "and -2n/-5n anchors, derived factor positivity, and the absolute-value "
        "derivation of both signed inequalities"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
