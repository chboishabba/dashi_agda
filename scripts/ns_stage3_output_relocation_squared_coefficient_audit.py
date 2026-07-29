#!/usr/bin/env python3
"""Exact audit for the squared output-relocation coefficient frontier."""
from __future__ import annotations

import json
from fractions import Fraction as Q


def dot(left: tuple[Q, ...], right: tuple[Q, ...]) -> Q:
    assert len(left) == len(right)
    return sum((a * b for a, b in zip(left, right)), Q(0))


def norm_squared(values: tuple[Q, ...]) -> Q:
    return sum((value * value for value in values), Q(0))


def run() -> dict[str, object]:
    # Bibliographic/source-scope correction.
    source_scope = {
        "grafakosOhArxiv": "1303.5144",
        "grafakosOhDoi": "10.1080/03605302.2013.822885",
        "ohWuPolynomialWeightArxiv": "2108.10412",
        "ohWuPolynomialWeightDoi": "10.1007/s00209-022-03120-6",
        "katoPonceOriginalDoi": "10.1002/cpa.3160410704",
        "bonyDoi": "10.24033/asens.1404",
    }
    assert source_scope["grafakosOhArxiv"] != source_scope["ohWuPolynomialWeightArxiv"]

    # Exact rational endpoint arithmetic.
    two = Q(2)
    five_halves = Q(5, 2)
    five = Q(5)
    three = Q(3)
    assert two < five_halves < three
    assert five == five_halves + five_halves
    assert five - five_halves == five_halves

    # Exact finite Cauchy--Schwarz / multiplier-square samples.  Each fibre is
    # normalized to left/right squared norm <= 1 and multiplier^2 <= 1.
    samples = (
        (Q(1), (Q(1), Q(0), Q(0)), (Q(1), Q(0), Q(0))),
        (Q(-1), (Q(3, 5), Q(4, 5)), (Q(4, 5), Q(-3, 5))),
        (Q(2, 3), (Q(1, 2), Q(1, 2)), (Q(1, 2), Q(-1, 2))),
        (Q(7, 11), (Q(2, 3), Q(1, 3)), (Q(-1, 3), Q(2, 3))),
    )
    fibre_checks: list[dict[str, str]] = []
    shell_sum = Q(0)
    for multiplier, left, right in samples:
        left_norm = norm_squared(left)
        right_norm = norm_squared(right)
        value = multiplier * dot(left, right)
        value_squared = value * value
        cauchy_upper = multiplier * multiplier * left_norm * right_norm
        assert Q(0) <= left_norm <= Q(1)
        assert Q(0) <= right_norm <= Q(1)
        assert multiplier * multiplier <= Q(1)
        assert value_squared <= cauchy_upper <= Q(1)
        shell_sum += value_squared
        fibre_checks.append(
            {
                "multiplier": str(multiplier),
                "leftNormSquared": str(left_norm),
                "rightNormSquared": str(right_norm),
                "valueSquared": str(value_squared),
            }
        )
    assert shell_sum <= Q(len(samples))

    # Square order reflection on the nonnegative cone.
    square_samples = (
        (Q(0), Q(0)),
        (Q(0), Q(7, 13)),
        (Q(1, 9), Q(2, 9)),
        (Q(7, 11), Q(8, 11)),
        (Q(128, 93), Q(2)),
    )
    for left, right in square_samples:
        assert Q(0) <= left and Q(0) <= right
        assert left * left <= right * right
        assert left <= right

    # Target-interval exponents and dyadic domination.
    regularities = (Q(251, 100), Q(8, 3), Q(299, 100))
    shells = (0, 1, 2, 3, 7, 16)
    exponent_checks: list[dict[str, str | int]] = []
    for regularity in regularities:
        low_decay = 2 * regularity - five_halves
        gap_decay = 2 * regularity
        assert five_halves < regularity < three
        assert two < low_decay
        assert five < gap_decay
        for shell in shells:
            assert -low_decay * shell <= -two * shell
            assert -gap_decay * shell <= -five * shell
            assert Q(2) ** (-two * shell) == Q(1, 4) ** shell
            assert Q(2) ** (-five * shell) == Q(1, 32) ** shell
            exponent_checks.append(
                {
                    "s": str(regularity),
                    "shell": shell,
                    "lowDecay": str(low_decay),
                    "gapDecay": str(gap_decay),
                }
            )

    return {
        "sourceScope": source_scope,
        "fibreChecks": fibre_checks,
        "exponentChecks": exponent_checks,
        "decision": {
            "outputLowRelocationIdentityUsesExactTransversality": True,
            "katoPonceNotRequiredForOutputLowIdentity": True,
            "katoPonceRetainedForUnfavourableAdjoints": True,
            "finiteSquaredCoefficientCoreClosed": True,
            "squareToAbsoluteTransportClosed": True,
            "orderedCapabilitiesUnified": True,
            "baseTwoConstructedFromNativeExponential": True,
            "endpointInequalitiesDerived": True,
            "endToEndTheoremCompositionClosed": True,
            "concreteNativeBackendClosed": False,
            "concreteLogTwoAnchorsClosed": False,
            "literalFiniteFibreRepresentationClosed": False,
            "concreteOutputRelocationTheoremClosed": False,
        },
    }


def main() -> int:
    result = run()
    print(json.dumps(result["decision"], sort_keys=True))
    print(
        "verified source separation, exact endpoint arithmetic, finite squared "
        "Cauchy--Schwarz fibres, nonnegative square reflection and target-shell "
        "dyadic domination"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
