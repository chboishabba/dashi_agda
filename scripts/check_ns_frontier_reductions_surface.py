#!/usr/bin/env python3
"""Fail-closed audit for exact reductions after the seven-leaf NS cutset."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

REQUIRED = {
    "NSPeriodicCoefficientUnitaryNormAdapter.agda": [
        "coefficientUnitaryToBernsteinAdapterInputs",
        "coefficientUnitaryOfficialNormIdentification",
        "coefficientUnitaryGlobalParseval",
        "coefficientUnitaryShellParseval",
        "coefficientUnitaryNormAdapterLevel = machineChecked",
    ],
    "NSPeriodicBiotSavartTransversality.agda": [
        "biotSavartVelocityIsTransverse",
        "biotSavartTransversalityAssemblyLevel = machineChecked",
    ],
    "NSPeriodicStrictDissipationMargin.agda": [
        "strictMarginNonnegative",
        "periodicNonlinearPlusStrictMarginBelowViscosity",
        "periodicNonlinearBelowViscosity",
    ],
    "NSPeriodicIntegratedExpenditureStrictMarginAdapter.agda": [
        "strictMarginPaysOfficialBudget",
        "strictMarginIntegratedWeightedShellEstimate",
        "strictMarginIntegratedVorticityEstimate",
        "strictMarginIntegratedBKMContinuation",
    ],
    "NSPeriodicPacketFractionQuotientSign.agda": [
        "quotientDerivativeFormula",
        "numeratorStrictlyPositive",
        "packetFractionDerivativeStrictlyPositive",
    ],
    "NSPeriodicNormalizedBoundaryCommonParameters.agda": [
        "selectedParametersAdmissible",
        "commonParametersToNormalizedBoundaryInputs",
        "commonParameterizedBoundaryHasNoFirstExit",
    ],
    "NSPeriodicNormalizedBoundaryCandidateTuple.agda": [
        "selectedNormalizedBoundaryCandidate",
        "selectedPacketOffPartition",
        "selectedGammaNumerator = refl",
        "selectedSizeSquaredCeiling = refl",
    ],
    "NSPeriodicHysteresisSeparation.agda": [
        "twoWayHysteresisRequiresDoubleModulus",
        "hysteresisGapExcludesImmediateBackSwitch",
    ],
    "NSPeriodicAdaptiveSwitchSeparationAdapter.agda": [
        "separationExcludesImmediateBackSwitch",
        "switchSeparationToAdaptiveSwitchInputs",
        "adaptiveSwitchControlFromSeparation",
    ],
    "NSPeriodicDiffuseDissipationCharging.agda": [
        "diffuseChargedVorticityBelowTotalBudget",
        "diffuseDissipationChargeGivesFiniteVorticity",
    ],
    "NSPeriodicDiffuseDissipationRouteAdapter.agda": [
        "diffuseDissipationRouteToBKMInputs",
        "diffuseDissipationRouteGivesBKM",
    ],
    "NSPeriodicZeroChartDiffuseSelection.agda": [
        "largePacketGivesChartOrDirectControl",
        "periodicZeroChartDiffuseSelection",
        "periodicCoverageClassAsDisjunction",
    ],
    "NSPeriodicExtendedCoverageBKM.agda": [
        "directBKMGivesVorticityControl",
        "periodicExtendedCoverageGivesVorticityControl",
    ],
    "NSPeriodicWeightedEnvelopeLimitTransport.agda": [
        "finitePartialPassesToUniformBound",
        "fullEnvelopeLeastUpperBound",
        "weightedEnvelopeTransportGivesFiniteContinuumVorticity",
    ],
    "NSPeriodicWeightedEnvelopeContinuumAdapter.agda": [
        "weightedEnvelopeVorticityBoundPassesToLimit",
    ],
    "NSPeriodicConcreteCutoffCubeCarrier.agda": [
        "signedIntervalNoDuplicates",
        "cutoffModeEnumerationComplete",
        "cutoffModeEnumerationSound",
        "cutoffModeEnumerationNoDuplicates",
        "literalCutoffCubeLength",
        "cutoffClosedUnderNegation",
        "zeroModeHandledExactlyOnce",
        "concreteCutoffCubeCarrierLevel = machineChecked",
    ],
    "NSPeriodicConcreteIntegerModeNorm.agda": [
        "nonzeroModeNatNormPositive",
        "embeddedNonzeroModeNormPositive",
        "concreteIntegerModeNormIdentification",
        "concreteModeInverseScaling",
        "concreteIntegerModeNormLevel = machineChecked",
    ],
    "NSPeriodicConcreteOfficialNormWeights.agda": [
        "literalL2Weight",
        "literalH1Weight",
        "literalShellWeightAt",
        "concreteCoefficientUnitaryNormCarrier",
        "concreteOfficialFiniteSumIdentification",
        "concreteOfficialNormWeightsLevel = machineChecked",
    ],
    "NSPeriodicCanonicalNearYoungAllocation.agda": [
        "nearPaymentsSumToQuarter",
        "interpretedNearPaymentDecomposes",
        "canonicalNearComponentsFitQuarter",
        "canonicalNearYoungAllocationLevel = machineChecked",
    ],
    "NSPeriodicConcreteCandidateBudgetArithmetic.agda": [
        "concreteNearAllocationIsQuarter",
        "concreteFarHighConstantProductIsEight",
        "farHighCandidateFitsCanonicalEighth",
        "concreteCandidateBudgetArithmeticLevel = machineChecked",
    ],
    "NSPeriodicCompactGammaPDEBalance.agda": [
        "componentBalancesCombine",
        "literalPotentialDerivativePDEBalance",
        "identifiedPotentialPDEBalance",
        "compactGammaPDEBalanceLevel = machineChecked",
    ],
    "NSPeriodicCanonicalThreeBoundaryTupleAdapter.agda": [
        "complementaryPacketOff",
        "canonicalTupleToThreeBoundaryMarginInputs",
        "canonicalTupleGivesThreeStrictBoundarySigns",
        "canonicalThreeBoundaryTupleAdapterLevel = machineChecked",
    ],
    "NSPeriodicObservableDerivativeBoundReduction.agda": [
        "quotientDerivativeUniform",
        "observableBoundsToScoreDerivativeInputs",
        "periodicScoreDerivativeUniformBound",
        "observableDerivativeBoundReductionLevel = machineChecked",
    ],
    "NSPeriodicDiffuseLowHighSplit.agda": [
        "lowHighPiecesBelowChargeAndRemainder",
        "lowHighSplitToDissipationCharge",
        "diffuseLowHighSplitGivesFiniteVorticity",
        "diffuseLowHighSplitLevel = machineChecked",
    ],
    "NSPeriodicChartFailureAnalyticRoutes.agda": [
        "badGammaVorticityEstimate",
        "badTailVorticityEstimate",
        "excessiveSizeVorticityEstimate",
        "analyticFailureRoutesToCoverageInputs",
        "largePacketGivesChartOrAnalyticBKM",
        "chartFailureAnalyticRoutesLevel = machineChecked",
    ],
    "NSPeriodicFixedShellFiniteRankConvergence.agda": [
        "finiteFoldConverges",
        "fixedFinitePartialConverges",
        "finitePartialLimitBelowUniformBound",
        "finiteShellInputsToWeightedEnvelopeLimit",
        "fixedShellFiniteRankConvergenceLevel = machineChecked",
    ],
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "sevenAnalyticLeafEndpointPromoted = true",
    "unconditionalPeriodicNavierStokesTheorem = true",
    "clayNavierStokesSubmissionPromoted = true",
)


def uncommented_agda(text: str) -> str:
    """Remove line comments before scanning for proof escape hatches."""
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def main() -> None:
    errors: list[str] = []
    for filename, tokens in REQUIRED.items():
        path = CLOSURE / filename
        if not path.is_file():
            errors.append(f"missing file: {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        code = uncommented_agda(text)
        for token in tokens:
            if token not in text:
                errors.append(f"{filename}: missing required token {token!r}")
        for token in FORBIDDEN:
            if token in code:
                errors.append(f"{filename}: forbidden token {token!r}")

    aggregate = (CLOSURE / "NSPairIncidenceKernelProgram.agda").read_text(
        encoding="utf-8"
    )
    regression = (CLOSURE / "NSPeriodicOfficialCompletionRegression.agda").read_text(
        encoding="utf-8"
    )
    for filename in REQUIRED:
        module_name = filename.removesuffix(".agda")
        if module_name not in aggregate:
            errors.append(f"aggregate missing import: {module_name}")
        if module_name not in regression:
            errors.append(f"regression missing import: {module_name}")

    if errors:
        for error in errors:
            print(f"[error] {error}")
        raise SystemExit(1)

    print(
        "[ok] exact periodic NS frontier reductions are present, wired, "
        "placeholder-free, and fail-closed"
    )


if __name__ == "__main__":
    main()
