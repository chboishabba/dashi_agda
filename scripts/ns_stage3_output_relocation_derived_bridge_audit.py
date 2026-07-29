#!/usr/bin/env python3
"""Exact audit for derived output-relocation power and signed bridges."""
from __future__ import annotations

import json
from fractions import Fraction as Q


def run() -> dict[str, object]:
    regularities = (Q(251, 100), Q(8, 3), Q(299, 100))
    shells = (0, 1, 2, 3, 7, 16, 64)

    exponent_checks: list[dict[str, str | int]] = []
    for regularity in regularities:
        low_decay = 2 * regularity - Q(5, 2)
        gap_decay = 2 * regularity
        assert regularity > Q(5, 2)
        assert low_decay >= 2
        assert gap_decay >= 5

        for shell in shells:
            # Multiplication by a nonnegative natural preserves order, then
            # negation reverses it.
            assert 2 * shell <= low_decay * shell
            assert -low_decay * shell <= -2 * shell
            assert 5 * shell <= gap_decay * shell
            assert -gap_decay * shell <= -5 * shell

            # Exact integer anchors used by the Agda theorem.
            quarter_anchor = Q(1, 4) ** shell
            thirty_second_anchor = Q(1, 32) ** shell
            assert quarter_anchor == Q(1, 2) ** (2 * shell)
            assert thirty_second_anchor == Q(1, 2) ** (5 * shell)

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
        "verified exact exponent-order reversal, natural-shell scaling, "
        "the -2n/-5n rational anchors, and absolute-value derivation of both "
        "signed coefficient inequalities"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
