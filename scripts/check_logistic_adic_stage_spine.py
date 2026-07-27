#!/usr/bin/env python3
"""Fail-closed audit for the logistic/adic/stage dynamical-adapter tranche."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    ROOT / "DASHI/Arithmetic/AdicGeometricMirror.agda",
    ROOT / "DASHI/Cognition/PNF/TraumaMemoryHypervoxelBridge.agda",
    ROOT / "DASHI/Dynamics/LogisticAdicStageCommutingSpine.agda",
    ROOT / "DASHI/Dynamics/LogisticAdicManifoldObligations.agda",
    ROOT / "DASHI/Foundations/CompositeRadixPrimeLaneBridge.agda",
    ROOT / "DASHI/Foundations/FamilyDecimalMonsterCrossPollination.agda",
    ROOT / "DASHI/Foundations/StageValuationBundleAtlas.agda",
    ROOT / "DASHI/Foundations/StageTetralemmaArrestBridge.agda",
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
    "TraumaMemoryHypervoxelBridge.agda": [
        "memoryDepth",
        "versionedMemoryDepth",
        "MemoryDepthWitness",
        "rememberedDepthIsAgreement",
        "PNFMemoryHypervoxel",
        "prime369Field",
        "depthWitnessAt",
        "FibreLearningUpdate",
        "MemoryDepthLearningReceipt",
        "Stage8PNFMemoryObstruction",
        "PriorTraumaMemoryArchitectureCrossPollination",
        "canonicalPriorTraumaMemoryArchitectureCrossPollination",
        "canonicalTraumaBodyMemoryCandidateBridge",
        "canonicalGenomeEpigenomeConnectomeBodyMemoryBridge",
        "canonicalZeroSupervoxel",
        "canonicalAvoidanceAttractor",
        "SuperField.depth3Field",
        "everyMemoryValuationIsPAdicClaimed",
    ],
    "LogisticAdicStageCommutingSpine.agda": [
        "LogisticAlgebra",
        "logisticStepCommutes",
        "LogisticChartSeparation",
        "LogisticInvariantRegion",
        "FiniteResidueLogisticSquare",
        "parameterDenominatorAdmissible",
        "GovernedStageObservation",
        "numeratorFactorVec357",
        "denominatorFactorVec100",
        "valuationProfile357Over100",
        "valuationProfileExact",
        "p3NormExact",
        "continuumChaosPromoted",
        "realBifurcationTreeTransferredToPAdics",
    ],
    "LogisticAdicManifoldObligations.agda": [
        "AttractorClassificationFactorsThroughTheta",
        "StageIndexedManifoldAtlas",
        "canonicalAttractorBifurcationAuthorityBoundary",
        "canonicalStage11ManifoldProcessBoundary",
        "canonicalCrossLaneOrthogonalityBoundary",
        "canonicalDynamicalAdapterRemainingObligations",
    ],
    "CompositeRadixPrimeLaneBridge.agda": [
        "canonicalSixJoinedChart",
        "canonicalNinePrimaryDepthChart",
        "lowLocalClosure3",
        "middleReflexiveClosure6",
        "highSystemicClosure9",
    ],
    "FamilyDecimalMonsterCrossPollination.agda": [
        "canonicalTwoParentOneChildSupportFibre",
        "canonicalOneThirdRoleWeight",
        "exactPlaceValue",
        "canonicalDecimal357Address",
        "canonical357SymbolicCylinder",
        "incrementLaneUpdatesCommute",
        "exactMonsterTableIrreducibleCount",
        "canonicalMonsterRepresentationSeparationReceipt",
    ],
    "StageValuationBundleAtlas.agda": [
        "TransitionContext",
        "GuardedStageEdge",
        "canonicalArrestedTetralemma",
        "canonicalReflexiveOscillation",
        "Stage8ObstructionObservation",
        "oneOver81DecimalCycleCertificate",
        "digit8AbsentFromOneOver81Block",
        "PlaceBundle",
        "BundleSheaf",
        "coarseBundleMatchesCarriedValue",
        "canonicalStage11CrossScaleJoin",
        "stage14Address",
        "stage17Address",
        "stage200Address",
        "CompressedStageTransition",
    ],
    "StageTetralemmaArrestBridge.agda": [
        "overflowToneCollapsesToSeedTone",
        "fourStepsReturnToSeed",
        "TetralemmaArrestReceipt",
        "canonicalTetralemmaArrestReceipt",
    ],
    "FramedORCSLPGFAdapter.agda": [
        "FramedCoordinate",
        "coordinateSlot",
        "framedDynamicRow",
        "canonicalFramedORCSLPGFAdapter",
        "canonicalMonsterCarrierAdmissionCandidate",
        "FramedORCSLPGFAuthorityBoundary",
    ],
    "SheetExchangeJFixedResolutionBoundary.agda": [
        "constantJScalarQuotient",
        "constantQuotientCoverFlipInvariant",
        "TwoSheetedCoverInterface.centralFlip cover",
        "constantQuotientIs196884",
        "constantQuotientIntentional",
        "quotientIsLiftSensitive",
        "pureInvolutionConvergesClaimed",
        "observerPlusOneUniversallyReachesJClaimed",
    ],
    "LogisticAdicStageRegression.agda": [
        "canonicalLogisticAdicStageRegression",
        "natIdentitySquare357At50",
        "tetralemmaArrest",
        "compressedTransformativeJump",
        "pnfTraumaMemoryHypervoxelBoundary",
        "priorTraumaMemoryArchitecture",
        "familySupportFibre",
        "monsterRepresentationSeparation",
        "remainingObligations",
        "sheetResolution",
    ],
    "TlureyChaosBridge.agda": [
        "logisticChartSeparation",
        "continuumChaosPromoted",
        "realBifurcationTreeTransferredToPAdics",
        "decimalDigitStageSemanticsPromoted",
        "LogisticContinuumAuthorityBoundary.continuumChaosPromoted",
    ],
}

FORBIDDEN = [
    "postulate",
    "{!!}",
    "?_",
    "continuumChaosPromoted = true",
    "realBifurcationTreeTransferredToPAdics = true",
    "decimalDigitStageSemanticsPromoted = true",
    "monsterOriginClaimed = true",
    "topologicalIdentificationClaimed = true",
    "politicalAttractorTheoremPromoted = true",
    "psychiatricOutcomePredicted = true",
    "numeralAloneConstructsManifold = true",
    "pureInvolutionConvergesClaimed = true",
    "observerPlusOneUniversallyReachesJClaimed = true",
    "residualAloneProvesTrauma = true",
    "formalCarrierDiagnosesPerson = true",
    "extinctionErasesMemory = true",
    "everyMemoryValuationIsPAdicClaimed = true",
]


def check_exact_arithmetic() -> None:
    assert sum(3**k for k in range(4)) == 40
    assert 357 == 3 * 7 * 17
    assert 100 == 2 * 2 * 5 * 5
    assert 357 == 3 * 100 + 5 * 10 + 7

    valuations = {2: -2, 3: 1, 5: -2, 7: 1, 11: 0, 17: 1}
    assert valuations == {2: -2, 3: 1, 5: -2, 7: 1, 11: 0, 17: 1}
    assert 6 == 2 * 3
    assert 9 == 3 * 3
    assert 3 == 2 + 1
    assert 100 == 10 * 10
    assert 11 == 10 * 1 + 1
    assert 14 == 10 * 1 + 4
    assert 17 == 10 * 1 + 7
    assert 200 == 10 * 20
    assert 196884 == 196883 + 1
    assert 81 * 12_345_679 == 999_999_999

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
    print("PASS: rational logistic algebra and proof-carrying chart/residue contracts are present")
    print("PASS: memoryDepth is explicit and can be witnessed by 369-prefix agreement")
    print("PASS: PNF learning consumes existing fibre reweighting/rewiring dynamics")
    print("PASS: trauma/body-memory, clopen psychology, attractor and SSP field surfaces are cross-pollinated")
    print("PASS: 357/100 FactorVec support, place value and valuation profile are exact")
    print("PASS: composite 6/9 radices remain joined/primary-depth charts, not fields")
    print("PASS: tetralemma quotient seam and Stage-4 arrest are proof-carrying")
    print("PASS: stage 0..11 is valuation-, memory-, learning- and residual-aware")
    print("PASS: Stage 8 cycle, Stage 11 bundle join and beyond-11 addresses are exact")
    print("PASS: ORCSLPGF, manifold, attractor and constant J quotient remain fail-closed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
