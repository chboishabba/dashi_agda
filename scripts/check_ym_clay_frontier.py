#!/usr/bin/env python3
"""Fail-closed textual audit for the explicit P1--P5 Yang--Mills frontier.

The script checks declaration integrity, literature metadata and the honesty
ledger. It does not replace the Agda kernel. The configured Green closure is
delegated to its own stricter audit so the finite inverse and analytic producer
cuts cannot drift.
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
        "activityNonnegative",
        "actionFactorNonnegative",
        "physicalProductBelowCertifiedProduct",
        "wilsonActivityPerTraversalBelowOneSixteenth",
        "wilsonActivityAbsoluteSignConventionLevel = machineChecked",
        "DOI: 10.1007/BF01211762",
        "DOI: 10.1007/s00220-007-0279-2",
        "literalWilsonSixFactorBoundsLevel = conditional",
    ),
    YM / "BalabanClayT2TraversalRootedShellExact.agda": (
        "the exact 8/16 Kotecký--Preiss specialisation",
        "DOI: 10.1007/BF01211762",
        "eightTimesOneSixteenthIsHalf",
        "activityPerExtensionBelowOneSixteenth",
        "oneTraversalStepBelowHalf",
        "rootedShellBelowQuarterHalfPower",
        "traversalSuppressionImpliesFiniteKP",
        "rootedTraversalCriterionIsKPLevel = machineChecked",
        "wilsonActivityPerTraversalBelowOneSixteenthLevel = conditional",
    ),
    YM / "BalabanClayT2ClusterCriterionComparisonExact.agda": (
        "R. Kotecký and D. Preiss",
        "DOI: 10.1007/BF01211762",
        "R. Fernández and A. Procacci",
        "DOI: 10.1007/s00220-007-0279-2",
        "R. Bissacot, R. Fernández and A. Procacci",
        "DOI: 10.1007/s10955-010-9956-1",
        "C. Gruber and H. Kunz",
        "DOI: 10.1007/BF01651334",
        "KoteckyPreissCriterion",
        "DobrushinCriterion",
        "FernandezProcacciCriterion",
        "dobrushinBelowKP",
        "fernandezProcacciBelowDobrushin",
        "koteckyPreissImpliesDobrushin",
        "dobrushinImpliesFernandezProcacci",
        "ExtendedGruberKunzIdentification",
        "fernandezProcacciImpliesExtendedGruberKunz",
        "physicalStrictCriterionSlackLevel = conditional",
        "physicalExtendedGKIdentificationLevel = conditional",
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
        "E. V. Haynsworth",
        "DOI: 10.1016/0024-3795(68)90050-5",
        "OperatorSchurData",
        "schurHessian",
        "operatorSchurEnergyExact",
        "operatorExactSchurComplement",
        "operatorSchurAlgebraVersusCoercivityBoundaryLevel = machineChecked",
        "physicalFluctuationSchurInputsLevel = conditional",
    ),
    YM / "BalabanClayT3UniformFluctuationSchurExact.agda": (
        "UniformFluctuationSchurFamily",
        "uniformFluctuationBlockCoercive",
        "uniformFluctuationCoefficientPositive",
        "exactSchurComplementAt",
        "DOI: 10.1016/0024-3795(68)90050-5",
        "physicalUniformFluctuationInputsLevel = conditional",
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
    YM / "BalabanClayT4BetaNormalizationConventionExact.agda": (
        "D. J. Gross and F. Wilczek",
        "DOI: 10.1103/PhysRevLett.30.1343",
        "H. D. Politzer",
        "DOI: 10.1103/PhysRevLett.30.1346",
        "R. Dashen and D. J. Gross",
        "DOI: 10.1103/PhysRevD.23.2340",
        "pureYMBetaZero",
        "inverseCouplingFromBetaDerivative",
        "inverseCouplingIsElevenOverTwentyFour",
        "inverseCouplingIsBetaZeroOverEight",
        "physicalPlaquetteCoefficientIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT4RunningCouplingConventionBridgeExact.agda": (
        "ConventionMatchedRunningCoupling",
        "betaLogBlockingUsesElevenOverTwentyFour",
        "betaLogBlockingUsesBetaZeroOverEight",
        "DOI: 10.1103/PhysRevD.23.2340",
        "physicalRunningCouplingCoefficientCalculationLevel = conditional",
    ),
    YM / "BalabanDashenGrossCalibration.agda": (
        "R. Dashen and D. J. Gross",
        "DOI: 10.1103/PhysRevD.23.2340",
        "calibratedConvention",
        "dashenGrossBibliographicConventionLevel = machineChecked",
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
        "K. Osterwalder and R. Schrader",
        "DOI: 10.1007/BF01645738",
        "DOI: 10.1007/BF01608978",
        "SequentiallyClosedProperty",
        "continuumNormalized",
        "continuumPositive",
        "continuumGaugeInvariant",
        "continuumReflectionPositive",
        "osClosureRequiresGramTopologyLevel = machineChecked",
        "nonzeroFourthCumulantExcludesGaussian",
        "physicalLimitTightnessAndNontrivialityLevel = conditional",
    ),
    YM / "BalabanClayT5OSGramTopologyExact.agda": (
        "K. Osterwalder and R. Schrader",
        "DOI: 10.1007/BF01645738",
        "DOI: 10.1007/BF01608978",
        "P. Menotti and A. Pelissetto",
        "DOI: 10.1007/BF01221251",
        "OSGramLimitData",
        "gramQuadraticFormConverges",
        "continuumReflectionPositiveFromGramTopology",
        "measureLimitReflectionPositive",
        "physicalOSGramTopologyIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT5OSGramClosedPropertyExact.agda": (
        "MeasureTopologyControlsOSGram",
        "measureConvergenceImpliesGramConvergence",
        "measureReflectionPositiveClosed",
        "reflectionPositiveSequentiallyClosed",
        "DOI: 10.1007/BF01645738",
        "DOI: 10.1007/BF01608978",
        "physicalMeasureToOSGramContinuityLevel = conditional",
    ),
    YM / "BalabanClayConstructiveProducerAdvance.agda": (
        "BalabanClayT1CommonAnalyticContractionExact",
        "BalabanClayT2ClusterCriterionComparisonExact",
        "BalabanClayT3UniformFluctuationSchurExact",
        "BalabanClayT4BetaNormalizationConventionExact",
        "BalabanClayT4RunningCouplingConventionBridgeExact",
        "BalabanClayT5OSGramTopologyExact",
        "BalabanClayT5OSGramClosedPropertyExact",
    ),
    YM / "BalabanClayFrontierCompletionLedger.agda": (
        "configuredMatrixActionLinearityLevel = machineChecked",
        "constructiveConfiguredFiniteInverseLevel = machineChecked",
        "t1CommonAnalyticContractionLevel = machineChecked",
        "t2KoteckyPreissToDobrushinLevel = machineChecked",
        "t2DobrushinToFernandezProcacciLevel = machineChecked",
        "t2FernandezProcacciToExtendedGKLevel = machineChecked",
        "t3UniformFluctuationCoercivityReductionLevel = machineChecked",
        "t4BetaZeroOverEightEqualsElevenOverTwentyFourLevel = machineChecked",
        "t4RunningCouplingConventionBridgeLevel = machineChecked",
        "p5OSGramQuadraticFormClosureLevel = machineChecked",
        "p5OSReflectionClosedPropertyLevel = machineChecked",
        "p1NonlinearMinimizingBackgroundLevel = conditional",
        "p2PhysicalActivityAndRootedShellEstimateLevel = conditional",
        "p2PhysicalExtendedGKIdentificationLevel = conditional",
        "p3UniformFluctuationCoercivityInputsLevel = conditional",
        "p4PhysicalPlaquetteCoefficientIdentificationLevel = conditional",
        "p5PhysicalOSGramTopologyIdentificationLevel = conditional",
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
        "The frontier audit now records the source-accurate hierarchy KP -> "
        "Dobrushin -> Fernandez-Procacci, with extended Gruber-Kunz requiring "
        "an explicit subset-polymer identification and all activities treated as "
        "nonnegative absolute majorants. It separates Schur algebra from uniform "
        "fluctuation coercivity, proves beta_0/(8 pi^2) = 11 C_A/(24 pi^2), "
        "and requires convergence of complete OS Gram quadratic forms rather than "
        "bare pointwise correlators. Authors, titles and DOI metadata are pinned "
        "in the relevant Agda modules. Literal Wilson/Haar identifications remain "
        "conditional; no kernel receipt is fabricated."
    )


if __name__ == "__main__":
    main()
