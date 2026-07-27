#!/usr/bin/env python3
"""Fail-closed textual audit for the explicit P1--P5 Yang--Mills frontier.

The script checks declaration integrity and the honesty ledger. It does not
replace the Agda kernel. The configured Green closure is delegated to its own
stricter audit so the finite inverse and analytic producer cuts cannot drift.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanSU2RationalAdjointRadiusExact.agda": (
        "adjointDisplacementWithUnitDefectExact",
        "adjointDisplacementRadiusBound",
        "su2PhysicalLinkRadiusProducerLevel = conditional",
    ),
    YM / "BalabanSU2RationalWilsonLargeFieldGapExact.agda": (
        "unitChordalEqualsTwiceTraceDeficit",
        "localWilsonActionGap",
        "largeFieldActionLowerBoundFromWitnesses",
        "largeFieldDuplicateFreeWitnessGeometryLevel = conditional",
    ),
    YM / "BalabanClayP1BackgroundStabilityExact.agda": (
        "RegularBackgroundConstruction",
        "backgroundRelativeFormSmallness",
        "smallBackgroundOneThirtySecondCoercivity",
        "p1MinimizingBackgroundProducerLevel = conditional",
        "p1FiveUniformComponentEstimatesLevel = conditional",
    ),
    YM / "BalabanClayP1PicardBackgroundConstructionExact.agda": (
        "picardBackgroundCore",
        "picardBackgroundCoreFixed",
        "fixedPointUniqueCore",
        "backgroundSatisfiesConstraint",
        "backgroundGaugeFixed",
        "backgroundStationary",
        "minimizerUniqueModuloGauge",
        "backgroundRegularity",
        "picardRegularBackgroundConstruction",
        "p1LiteralWilsonPicardInputsLevel = conditional",
    ),
    YM / "BalabanClayT1CommonAnalyticContractionExact.agda": (
        "CommonAnalyticCriticalMap",
        "criticalMapContraction",
        "criticalMapPreservesCommonBall",
        "CommonSecondJetEnvelope",
        "commonSecondJetBound",
        "t1LiteralWilsonCommonNormInputsLevel = conditional",
    ),
    YM / "BalabanClayP2LargeFieldStepVExact.agda": (
        "GaugeInvariantBadBlockDecomposition",
        "LargeFieldActivityFactorization",
        "uniformFiniteVolumeKoteckyPreiss",
        "p2PhysicalActivityShellProducerLevel = conditional",
        "p2InfiniteClusterAndCorrelationProducerLevel = conditional",
    ),
    YM / "BalabanClayP2BadComponentGeometryExact.agda": (
        "BadPath",
        "everyBadBlockAssigned",
        "componentConnected",
        "sameComponentUnique",
        "badBlockGaugeInvariantForward",
        "badBlockGaugeInvariantBackward",
        "badBlockMeasurable",
        "p2LiteralWilsonBadPredicateInstantiationLevel = conditional",
    ),
    YM / "BalabanClayT2WilsonActivityFactorProductExact.agda": (
        "WilsonTraversalActivityFactors",
        "physicalProductBelowCertifiedProduct",
        "wilsonActivityPerTraversalBelowOneSixteenth",
        "literalWilsonSixFactorBoundsLevel = conditional",
    ),
    YM / "BalabanClayT2TraversalRootedShellExact.agda": (
        "eightTimesOneSixteenthIsHalf",
        "activityPerExtensionBelowOneSixteenth",
        "oneTraversalStepBelowHalf",
        "rootedShellBelowQuarterHalfPower",
        "traversalSuppressionImpliesFiniteKP",
        "wilsonActivityPerTraversalBelowOneSixteenthLevel = conditional",
    ),
    YM / "BalabanClayT2UrsellCauchyExact.agda": (
        "geometricTailBelow",
        "ursellTailBelowGeometric",
        "ursellCauchyTail",
        "connectedCorrelationExponentialDecay",
        "physicalUrsellTreeGraphMajorantLevel = conditional",
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
    YM / "BalabanClayP3FiniteConstrainedIntegralExact.agda": (
        "coarseMatchesSound",
        "coarseMatchesComplete",
        "smallLargePartitionListExact",
        "smallLargePartitionExact",
        "effectiveActionDefinesIntegral",
        "finiteExactOneStepIntegral",
        "p3CompactHaarIntegralLimitLevel = conditional",
    ),
    YM / "BalabanClayP3PrincipalFibreCoordinatesExact.agda": (
        "reconstructs",
        "fluctuationSatisfiesConstraint",
        "backgroundUnique",
        "fluctuationUnique",
        "jacobianExact",
        "p3LiteralWilsonPrincipalFibreInstantiationLevel = conditional",
    ),
    YM / "BalabanClayT3CompactHaarLimitExact.agda": (
        "CompactHaarQuadratureLimit",
        "smallLargeHaarPartitionExact",
        "constrainedHaarGaugeInvariant",
        "haarEffectiveActionDefinesIntegral",
        "productHaarQuadratureIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT3OperatorSchurComplementExact.agda": (
        "OperatorSchurData",
        "schurHessian",
        "operatorSchurEnergyExact",
        "operatorExactSchurComplement",
        "physicalFluctuationSchurInputsLevel = conditional",
    ),
    YM / "BalabanClayT3SchurWardBetaExact.agda": (
        "scalarSchurDefectIdentity",
        "scalarSchurEnergyExact",
        "fluctuationIntegralGaugeInvariant",
        "localizationPreservesWardIdentity",
        "quarticGeometricIdentity",
        "quarticRemainderPartialBound",
        "physicalWardBetaIdentificationLevel = conditional",
    ),
    YM / "BalabanClayP4DyadicCoercivityBudgetExact.agda": (
        "lossBudgetIdentity",
        "lossPartialSumBelowOneSixtyFourth",
        "uniformOneSixtyFourthCoercivity",
        "physicalOneStepLossEstimateLevel = conditional",
    ),
    YM / "BalabanClayP4CommonParameterDomainExact.agda": (
        "canonicalClayParameters",
        "canonicalDomainIsCommon",
        "canonicalBackgroundConstraintProducerLevel = conditional",
        "canonicalContinuumConstraintProducerLevel = conditional",
    ),
    YM / "BalabanClayT4CanonicalScalarWitnessExact.agda": (
        "PositiveMargin",
        "canonicalContractionMargin",
        "canonicalKPMargin",
        "canonicalOneStepMargin",
        "canonicalBetaRemainderMargin",
        "canonicalMassSurvivalMargin",
        "canonicalScalarCutset",
        "canonicalPhysicalConstantIdentificationLevel = conditional",
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
    YM / "BalabanClayT5PhysicalMassTransportExact.agda": (
        "partialFrom",
        "gapAtDepthBelowInitialPlusDefects",
        "terminalMassBelowInitialPlusBudget",
        "positivePhysicalMassSurvives",
        "terminalGapIsLambdaMultiple",
        "physicalTransferOperatorInterlacingLevel = conditional",
    ),
    YM / "BalabanClayT5LimitAndNontrivialityExact.agda": (
        "SequentiallyClosedProperty",
        "continuumNormalized",
        "continuumPositive",
        "continuumGaugeInvariant",
        "continuumReflectionPositive",
        "nonzeroFourthCumulantExcludesGaussian",
        "physicalLimitTightnessAndNontrivialityLevel = conditional",
    ),
    YM / "BalabanClayConstructiveProducerAdvance.agda": (
        "BalabanClayT1CommonAnalyticContractionExact",
        "BalabanClayT2WilsonActivityFactorProductExact",
        "BalabanClayT2TraversalRootedShellExact",
        "BalabanClayT2UrsellCauchyExact",
        "BalabanClayT3CompactHaarLimitExact",
        "BalabanClayT3OperatorSchurComplementExact",
        "BalabanClayT3SchurWardBetaExact",
        "BalabanClayT4CanonicalScalarWitnessExact",
        "BalabanClayT5PhysicalMassTransportExact",
        "BalabanClayT5LimitAndNontrivialityExact",
    ),
    YM / "BalabanClayFrontierCompletionLedger.agda": (
        "configuredMatrixActionLinearityLevel = machineChecked",
        "constructiveConfiguredFiniteInverseLevel = machineChecked",
        "t1CommonAnalyticContractionLevel = machineChecked",
        "t2WilsonActivityOneSixteenthLevel = machineChecked",
        "t2RootedShellQuarterHalfPowerLevel = machineChecked",
        "t2UrsellCauchyModulusLevel = machineChecked",
        "t3CompactHaarLimitAlgebraLevel = machineChecked",
        "t3OperatorSchurEnergyIdentityLevel = machineChecked",
        "t3OperatorSchurP3AdapterLevel = machineChecked",
        "t3QuarticBetaRemainderSummabilityLevel = machineChecked",
        "p4CanonicalScalarIntersectionLevel = machineChecked",
        "p5PhysicalMassInterlacingLevel = machineChecked",
        "p5SequentialOSPropertyClosureLevel = machineChecked",
        "p1NonlinearMinimizingBackgroundLevel = conditional",
        "p2PhysicalActivityAndRootedShellEstimateLevel = conditional",
        "p3ExactConstrainedIntegralCoordinatesLevel = conditional",
        "p4CanonicalCommonDomainInhabitationLevel = conditional",
        "p5ContinuumOSAndNontrivialityLevel = conditional",
        "branchHeadAuthoritativeAgda29TypecheckLevel = conditional",
    ),
}

FORBIDDEN = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Clay frontier audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, tokens in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in tokens:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    subprocess.run(
        [sys.executable, str(ROOT / "scripts/check_ym_configured_green_exact.py")],
        cwd=ROOT,
        check=True,
    )

    print(
        "The frontier branch now derives common-norm contraction/self-map, "
        "the six-factor Wilson activity product, exact 8/16 rooted-shell decay, "
        "an Ursell Cauchy modulus and correlation tail, compact-Haar limit "
        "algebra, scalar and operator Schur identities, exact gauge reindexing, "
        "quartic beta-remainder summability, one common scalar margin tuple, "
        "physical-mass interlacing, OS-property limit closure and fourth-"
        "cumulant nontriviality. Literal Wilson/Haar identifications remain "
        "explicit conditional producers; no kernel receipt is fabricated."
    )


if __name__ == "__main__":
    main()
