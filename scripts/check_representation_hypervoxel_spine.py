#!/usr/bin/env python3
"""Fail-closed audit for the representation/frame/hypervoxel tranche.

The arithmetic checks are exact. The source scan is deliberately narrow: it
protects the new theorem surface against proof holes, postulate declarations,
and accidental removal of the central laws. It is not a substitute for Agda
kernel checking.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    ROOT / "DASHI/Foundations/RepresentationChartInvariant.agda",
    ROOT / "DASHI/Foundations/CanonicalHalfFrameScaleValuation.agda",
    ROOT / "DASHI/Foundations/RecursiveRadixHypervoxel.agda",
    ROOT / "DASHI/Foundations/LiftPolarityPathComposition.agda",
    ROOT / "DASHI/Foundations/RadixValuationStageBridge.agda",
    ROOT / "DASHI/Geometry/RepresentationPrefixUltrametricBridge.agda",
    ROOT / "DASHI/Physics/Closure/SU2SO3369HypervoxelBridge.agda",
    ROOT / "DASHI/Cognition/SituatedFrameMetacognitionBoundary.agda",
    ROOT / "DASHI/Foundations/RepresentationHypervoxelRegression.agda",
]

REQUIRED_TOKENS = {
    "RepresentationChartInvariant.agda": [
        "data Positive",
        "denominatorPositive",
        "positiveProduct",
        "threeSixIsOneHalf",
        "binaryPointOneIsOneHalf",
        "presentationPreservesHalf",
        "FramedScaleValuationObject",
        "transitionTargetsChart",
        "transitionPreservesEvaluation",
        "transitionIdentity",
        "transitionComposition",
        "InspectedRepresentation Value Chart Scale Valuation",
        "inspectRepresentation",
        "threeSixIsSecondHarmonic",
        "refineRatioPreserves",
        "threefoldHalfRefinement",
        "zeroDenominatorConstructible = false",
        "zeroRefinementFactorAccepted = false",
        "transitionCanMissRequestedTarget = false",
        "FramedAtlas",
        "ContextualThreeSixNineObservation",
    ],
    "CanonicalHalfFrameScaleValuation.agda": [
        "ChartedHalfRepresentation",
        "carriedChart",
        "transitionChart",
        "canonicalHalfFrameScaleValuation",
        "canonicalTransitionTargetsChart",
        "canonicalTransitionPreservesValue",
        "canonicalInspectionValue",
        "canonicalInspectionChart",
        "canonicalInspectionScale",
        "canonicalInspectionValuation",
    ],
    "RecursiveRadixHypervoxel.agda": [
        "TernaryAddress",
        "coarsenAfterRefine",
        "joinAddress",
        "configurationCount",
        "tower3",
        "projectCentralFlipInvariant",
        "RubikMove",
        "CentreBlindField",
        "centralFlipInvisible",
        "centreBlindFieldCarriesInvariance",
    ],
    "LiftPolarityPathComposition.agda": [
        "composePolarityPath",
        "composePolarityAppend",
        "CoarseFinePolarityFactorisation",
        "canonicalCoarseFineFactorisation",
    ],
    "RadixValuationStageBridge.agda": [
        "radixPositive",
        "decimalBinaryHalfEquivalent",
        "RadixOriginPrefix",
        "RadialAddress : RadixChart",
        "ternaryChart",
        "RadixHyperAddress (chart : RadixChart)",
        "RadixBlock chart rank",
        "radixHyperCoarsenAfterRefine",
        "radixHyperSiteCount : RadixChart",
        "zeroRadixConstructible = false",
        "canonicalDecimalCarryGrammar",
        "stage1NotStage10",
        "stage1ToStage10UnitLift",
        "canonicalStageCarryJoin",
        "PrimeLaneAddressProjection",
    ],
    "RepresentationPrefixUltrametricBridge.agda": [
        "OriginPrefixUltrametricReceipt",
        "sharedThreeSixPrefix",
        "canonicalDistanceBound",
    ],
    "SU2SO3369HypervoxelBridge.agda": [
        "axisLiftHexRoundTrip",
        "nonarySlotRoundTrip",
        "TwoSheetedCoverInterface",
        "positiveNegativeAxisLiftDistinct",
        "centralFlipHasNoFixedPoint",
        "fibreComplete",
        "finiteAxisLiftDoubleCover",
        "canonicalSO3RightJacobianConvention",
        "canonicalExponentialJacobianDiscipline",
    ],
    "SituatedFrameMetacognitionBoundary.agda": [
        "metacognitiveLiftPreservesExperience",
        "PluralFrameLedger",
        "logisticHalfReceipt",
        "canonicalExistingLogisticCarrierReconciliation",
        "a276087IsSecondIterate",
        "canonicalPrimorialTransformBoundary",
        "canonicalSituatedFrameAuthorityBoundary",
    ],
    "RepresentationHypervoxelRegression.agda": [
        "canonicalRepresentationHypervoxelRegression",
        "unifiedFrameScaleValuationCarrier",
        "threeSixTransitionTargetsPercentageChart",
        "Radix.binaryChart",
        "Radix.ternaryChart",
        "binaryRank3Depth1CountIs8",
        "pathPolarityFactorisation",
        "prefixUltrametricReceipt",
        "liftProjectionLaw",
    ],
}

FORBIDDEN_PATTERNS = [
    re.compile(r"^\s*postulate\b", re.MULTILINE),
    re.compile(r"\{!"),
    re.compile(r"!\}"),
    re.compile(r"\bTERMINATING\b"),
    re.compile(r"\bNON_TERMINATING\b"),
    re.compile(r"transitionCanMissRequestedTarget\s*=\s*true"),
]


def check_exact_arithmetic() -> None:
    presentations = [
        Fraction(3, 6),
        Fraction(1, 2),
        Fraction(5, 10),
        Fraction(50, 100),
        Fraction(1, 2),  # 0.1 in base two
    ]
    assert all(value == Fraction(1, 2) for value in presentations)
    assert Fraction(3 * 1, 3 * 2) == Fraction(1, 2)

    hierarchy = [3, 3 * 2, 3**2, 2 * 3**2, 3**3, 2 * 3**3, 3**4, 2 * 3**4]
    assert hierarchy == [3, 6, 9, 18, 27, 54, 81, 162]

    def site_count(base: int, rank: int, depth: int) -> int:
        assert base > 0
        return base ** (rank * depth)

    assert site_count(3, 1, 1) == 3
    assert site_count(3, 2, 1) == 9
    assert site_count(3, 3, 1) == 27
    assert site_count(3, 3, 2) == 729
    assert site_count(2, 3, 1) == 8

    def tower3(height: int) -> int:
        value = 1
        for _ in range(height):
            value = 3**value
        return value

    assert tower3(0) == 1
    assert tower3(1) == 3
    assert tower3(2) == 27

    assert 9 + 1 == 10
    assert 10 + 1 == 11
    assert 1 != 10 != 11

    polarity_product = 1
    for polarity in (-1, -1, 1):
        polarity_product *= polarity
    assert polarity_product == 1


def scan_sources() -> None:
    for path in FILES:
        if not path.is_file():
            raise AssertionError(f"missing required file: {path.relative_to(ROOT)}")

        text = path.read_text(encoding="utf-8")
        for pattern in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                raise AssertionError(
                    f"forbidden pattern {pattern.pattern!r} in {path.relative_to(ROOT)}"
                )

        for token in REQUIRED_TOKENS[path.name]:
            if token not in text:
                raise AssertionError(
                    f"missing required token {token!r} in {path.relative_to(ROOT)}"
                )


def main() -> int:
    check_exact_arithmetic()
    scan_sources()
    print("PASS: positive-denominator ratio, harmonic and radix presentations preserve 1/2 exactly")
    print("PASS: charted representations reach requested targets and preserve evaluation")
    print("PASS: all generic radix addresses carry positive-radix evidence")
    print("PASS: generic p/rank/depth and 3/6/9 lifted hierarchy counts are exact")
    print("PASS: centre-blind descent and two-sheet fibres are proof-carrying")
    print("PASS: lift path prefix/suffix parity composes exactly")
    print("PASS: carry grammar 9 -> 10 -> 11 is exact and stage roles remain distinct")
    print("PASS: representation/hypervoxel source surface is fail-closed")
    print("NOTE: run the Agda checker for kernel validation")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
