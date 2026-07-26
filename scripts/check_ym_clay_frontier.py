#!/usr/bin/env python3
"""Fail-closed textual audit for the explicit P1--P5 Yang--Mills frontier.

This script is narrower than Agda kernel validation. It checks that exact
reductions and the honest producer ledger remain present, and rejects postulates,
holes, unsafe termination and underscore proof bodies in the focused frontier
modules and repaired finite foundations.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanFiniteEnumerationDistinctExact.agda": (
        "zeroNotInSucMapGeneric",
        "zeroNotInSucMap",
        "allCyclicIndicesDuplicateFree",
        "cyclicZeroNotInSuccessorMapLevel = machineChecked",
    ),
    YM / "BalabanPhysicalBlockFibreSumsExact.agda": (
        "centeredDifferenceAlgebra",
        "scaledCenteredDifferenceExact",
        "scaledCenteredDifferenceSquareExact",
        "scaledCenteredFibreEnergyExact",
        "centeredSquareInductionAlgebra",
        "scaledVarianceNormalization",
        "physicalFibreCenteredDifferenceLevel = machineChecked",
    ),
    YM / "BalabanFourAxisMartingaleExact.agda": (
        "fourAxisMartingaleTelescopingRaw",
        "fourAxisMartingaleDecomposition",
        "fourSquareExpansionRaw",
        "pairCrossSumZero",
        "fourAxisMartingaleOrthogonalityImpliesVariance",
        "fourAxisVarianceDecomposition",
        "fourAxisMartingaleTelescopingLevel = machineChecked",
    ),
    YM / "BalabanConfiguredSide4ScalarWilsonOperatorExact.agda": (
        "siteSumProductZero",
        "firstBackwardPairing",
        "secondNegativeBackwardPairing",
        "planeTwoAxisPairingExact",
        "scalarPlanePairingExact",
        "scalarWilsonPlaneRieszLevel = machineChecked",
    ),
    YM / "BalabanConstructiveRationalMatrixInverseExact.agda": (
        "matrixProductActionExact",
        "matrixInverseLeftExact",
        "matrixInverseRightExact",
        "constructiveFiniteGreen",
        "constructivePointwiseGreenAssemblyLevel = machineChecked",
        "configuredGeneratedInverseProductProducerLevel = conditional",
    ),
    YM / "BalabanPath4SU2RationalMatrixCoordinatesExact.agda": (
        "deltaSumIdentity",
        "physicalCoordinateElementsDuplicateFree",
        "physicalFiniteRationalCoordinates",
        "tangentCoordinateRoundTripPointwise",
        "configuredGaugeFixedOperatorMatrix",
    ),
    YM / "BalabanPath4SU2RationalMatrixDimensionExact.agda": (
        "lengthCartesianExact",
        "siteCountExact",
        "positiveBondCountExact",
        "physicalCoordinateCountExact",
        "configuredMatrixDimensionIs3072",
        "configuredPhysicalMatrixDimensionLevel = machineChecked",
    ),
    YM / "BalabanPath4SU2ConfiguredMatrixActionExact.agda": (
        "configuredGaugeFixedMatrixAdd",
        "configuredGaugeFixedMatrixScale",
        "configuredGaugeFixedMatrixRespectsPointwise",
        "basisExpansionPointwise",
        "configuredMatrixActsExactly",
        "literalConfiguredMatrixActionCertificate",
        "configuredMatrixActionLinearityLevel = machineChecked",
    ),
    YM / "BalabanSU2RationalAdjointRadiusExact.agda": (
        "adjointDisplacementWithUnitDefectExact",
        "adjointDisplacementUnitExact",
        "adjointDisplacementPlusDiscardedSquareExact",
        "adjointDisplacementRadiusBound",
        "su2PhysicalLinkRadiusProducerLevel = conditional",
    ),
    YM / "BalabanSU2RationalWilsonLargeFieldGapExact.agda": (
        "unitChordalEqualsTwiceTraceDeficit",
        "wilsonActionEqualsHalfBetaChordal",
        "localWilsonActionGap",
        "largeFieldActionLowerBoundFromWitnesses",
        "largeFieldDuplicateFreeWitnessGeometryLevel = conditional",
    ),
    YM / "BalabanClayP1BackgroundStabilityExact.agda": (
        "RegularBackgroundConstruction",
        "backgroundHessianExact",
        "backgroundRelativeFormSmallness",
        "smallBackgroundOneThirtySecondCoercivity",
        "p1MinimizingBackgroundProducerLevel = conditional",
        "p1FiveUniformComponentEstimatesLevel = conditional",
    ),
    YM / "BalabanClayP2LargeFieldStepVExact.agda": (
        "GaugeInvariantBadBlockDecomposition",
        "LargeFieldActivityFactorization",
        "uniformFiniteVolumeKoteckyPreiss",
        "etaGapPositive",
        "p2PhysicalActivityShellProducerLevel = conditional",
        "p2InfiniteClusterAndCorrelationProducerLevel = conditional",
    ),
    YM / "BalabanClayP3PhysicalOneStepTransferExact.agda": (
        "ExactOneStepIntegral",
        "ExactNonlinearFluctuationCoordinates",
        "ExactSchurComplement",
        "oneStepPerturbationBound",
        "oneStepPhysicalCoercivityTransfer",
        "noGeneratedGaugeBosonMass",
        "RunningCouplingRecursion",
        "p3FivePhysicalComponentEstimateProducerLevel = conditional",
    ),
    YM / "BalabanClayP4DyadicCoercivityBudgetExact.agda": (
        "lossBudgetIdentity",
        "lossPartialSumBelowOneSixtyFourth",
        "uniformOneSixtyFourthCoercivity",
        "physicalOneStepLossEstimateLevel = conditional",
    ),
    YM / "BalabanClayP4CommonParameterDomainExact.agda": (
        "canonicalClayParameters",
        "canonicalBackgroundBudgetIdentity",
        "canonicalDomainIsCommon",
        "canonicalBackgroundConstraintProducerLevel = conditional",
        "canonicalContinuumConstraintProducerLevel = conditional",
    ),
    YM / "BalabanClayP5ContinuumMassGapExact.agda": (
        "AllScaleFiniteVolumeConstruction",
        "ThermodynamicLimit",
        "ContinuumLimit",
        "OsterwalderSchraderLimit",
        "physicalConnectedCorrelationBound",
        "positivePhysicalSpectralGap",
        "InteractingNontriviality",
        "p5NontrivialityProducerLevel = conditional",
    ),
    YM / "BalabanClayFrontierCompletionLedger.agda": (
        "fourAxisMartingaleScalarAlgebraLevel = machineChecked",
        "scalarWilsonRieszSignAndZeroFoldLevel = machineChecked",
        "finiteMatrixProductAndInverseConsequenceLevel = machineChecked",
        "physicalCoordinateEnumerationAndDeltaLevel = machineChecked",
        "configuredPhysicalMatrixDimension3072Level = machineChecked",
        "configuredGaugeFixedMatrixDefinitionLevel = machineChecked",
        "configuredMatrixActionLinearityLevel = machineChecked",
        "uniformOneSixtyFourthCoercivityLevel = machineChecked",
        "p1NonlinearMinimizingBackgroundLevel = conditional",
        "p2PhysicalActivityAndRootedShellEstimateLevel = conditional",
        "p3ConstructiveSchurComplementPropagatorLevel = conditional",
        "p5ContinuumOSAndNontrivialityLevel = conditional",
        "constructiveConfiguredFiniteInverseLevel = conditional",
        "branchHeadAuthoritativeAgda29TypecheckLevel = conditional",
    ),
}

FORBIDDEN_PATTERNS = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Clay frontier audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, required in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in required:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    aggregate = YM / "ConstructiveYangMillsNextSurface.agda"
    aggregate_text = aggregate.read_text(encoding="utf-8")
    for module in (
        "BalabanConfiguredSide4ScalarWilsonOperatorExact",
        "BalabanConstructiveRationalMatrixInverseExact",
        "BalabanPath4SU2RationalMatrixCoordinatesExact",
        "BalabanPath4SU2RationalMatrixDimensionExact",
        "BalabanPath4SU2ConfiguredMatrixActionExact",
        "BalabanSU2RationalAdjointRadiusExact",
        "BalabanSU2RationalWilsonLargeFieldGapExact",
        "BalabanClayP1BackgroundStabilityExact",
        "BalabanClayP2LargeFieldStepVExact",
        "BalabanClayP3PhysicalOneStepTransferExact",
        "BalabanClayP4DyadicCoercivityBudgetExact",
        "BalabanClayP4CommonParameterDomainExact",
        "BalabanClayP5ContinuumMassGapExact",
        "BalabanClayFrontierCompletionLedger",
    ):
        if module not in aggregate_text:
            fail(f"aggregate does not import {module}")

    print(
        "Finite martingale algebra, corrected scalar Wilson Riesz signs, the "
        "literal 3072-coordinate configured matrix action, constructive inverse "
        "consequences, P1--P5 reductions, numerical budgets and the honest "
        "producer ledger are present and hole-free."
    )


if __name__ == "__main__":
    main()
