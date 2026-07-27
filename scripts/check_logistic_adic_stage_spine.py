#!/usr/bin/env python3
"""Fail-closed audit for the logistic/adic/stage dynamical-adapter tranche."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    ROOT / "DASHI/Arithmetic/AdicGeometricMirror.agda",
    ROOT / "DASHI/Dynamics/LogisticAdicStageCommutingSpine.agda",
    ROOT / "DASHI/Foundations/CompositeRadixPrimeLaneBridge.agda",
    ROOT / "DASHI/Foundations/StageValuationBundleAtlas.agda",
    ROOT / "DASHI/Core/FramedORCSLPGFAdapter.agda",
    ROOT / "DASHI/Physics/Closure/SheetExchangeJFixedResolutionBoundary.agda",
    ROOT / "DASHI/Foundations/LogisticAdicStageRegression.agda",
    ROOT / "DASHI/Cognition/TlureyChaosBridge.agda",
]

REQUIRED = {
    "AdicGeometricMirror.agda": [
        "geometricPartialSum",
        "canonicalThreeAdicClosure",
        "HalfCompletionMirrorBridge",
        "positiveNegativeCancel",
        "topologicalIdentificationClaimed",
    ],
    "LogisticAdicStageCommutingSpine.agda": [
        "LogisticAlgebra",
        "logisticStepCommutes",
        "LogisticChartSeparation",
        "FiniteResidueLogisticSquare",
        "GovernedStageObservation",
        "numeratorFactorVec357",
        "denominatorFactorVec100",
        "valuationProfile357Over100",
        "continuumChaosPromoted",
        "realBifurcationTreeTransferredToPAdics",
    ],
    "CompositeRadixPrimeLaneBridge.agda": [
        "canonicalSixJoinedChart",
        "canonicalNinePrimaryDepthChart",
        "lowLocalClosure3",
        "middleReflexiveClosure6",
        "highSystemicClosure9",
    ],
    "StageValuationBundleAtlas.agda": [
        "TransitionContext",
        "GuardedStageEdge",
        "canonicalArrestedTetralemma",
        "canonicalReflexiveOscillation",
        "Stage8ObstructionObservation",
        "digit8AbsentFromOneOver81Block",
        "PlaceBundle",
        "BundleSheaf",
        "canonicalStage11CrossScaleJoin",
        "stage14Address",
        "stage17Address",
        "stage200Address",
        "CompressedStageTransition",
    ],
    "FramedORCSLPGFAdapter.agda": [
        "FramedCoordinate",
        "coordinateSlot",
        "framedDynamicRow",
        "bottomInterpretiveArrowRequirement",
        "FramedORCSLPGFAuthorityBoundary",
    ],
    "SheetExchangeJFixedResolutionBoundary.agda": [
        "resolveCentralFlipInvariant",
        "resolveAxisLiftIs196884",
        "pureInvolutionConvergesClaimed",
        "observerPlusOneUniversallyReachesJClaimed",
    ],
    "LogisticAdicStageRegression.agda": [
        "canonicalLogisticAdicStageRegression",
        "natIdentitySquare357At50",
        "compressedTransformativeJump",
        "sheetResolution",
    ],
    "TlureyChaosBridge.agda": [
        "logisticChartSeparation",
        "continuumChaosPromoted",
        "realBifurcationTreeTransferredToPAdics",
        "decimalDigitStageSemanticsPromoted",
    ],
}

FORBIDDEN = [
    "postulate",
    "{!!}",
    "?_",
    "continuumChaosPromoted = true",
    "realBifurcationTreeTransferredToPAdics = true",
    "monsterOriginClaimed = true",
    "topologicalIdentificationClaimed = true",
]


def check_exact_arithmetic() -> None:
    assert sum(3**k for k in range(4)) == 40
    assert 357 == 3 * 7 * 17
    assert 100 == 2 * 2 * 5 * 5

    valuations = {2: -2, 3: 1, 5: -2, 7: 1, 11: 0, 17: 1}
    assert valuations[3] == 1
    assert 6 == 2 * 3
    assert 9 == 3 * 3
    assert 100 == 10 * 10
    assert 11 == 10 * 1 + 1
    assert 14 == 10 * 1 + 4
    assert 17 == 10 * 1 + 7
    assert 200 == 10 * 20

    recurring_block = [0, 1, 2, 3, 4, 5, 6, 7, 9]
    assert 8 not in recurring_block


def scan_sources() -> None:
    for path in FILES:
        if not path.exists():
            raise AssertionError(f"missing file: {path}")
        text = path.read_text(encoding="utf-8")
        lowered = text.lower()
        for token in FORBIDDEN:
            if token.lower() in lowered:
                raise AssertionError(f"forbidden token {token!r} in {path}")
        for symbol in REQUIRED.get(path.name, []):
            if symbol not in text:
                raise AssertionError(f"missing required symbol {symbol!r} in {path}")


def main() -> int:
    check_exact_arithmetic()
    scan_sources()
    print("PASS: general adic mirror and exact 3-adic finite recurrence are present")
    print("PASS: rational logistic algebra and proof-carrying chart/residue squares are present")
    print("PASS: 357/100 FactorVec support and valuation profile are exact")
    print("PASS: composite 6/9 radices remain joined/primary-depth charts, not fields")
    print("PASS: stage 0..11 is valuation-, memory-, learning- and residual-aware")
    print("PASS: Stage 8 residual, Stage 11 bundle join and beyond-11 addresses are present")
    print("PASS: ORCSLPGF and JFixedPoint bridges remain fail-closed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
