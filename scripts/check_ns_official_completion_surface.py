#!/usr/bin/env python3
"""Audit the official-norm/expenditure/coverage Agda surface."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

FILES = {
    "NSPeriodicOfficialNormIdentification.agda": [
        "officialShellVorticityL2FromVelocity",
        "officialShellVorticityFromVelocity",
        "officialVorticityReconstruction",
        "officialPeriodicNormIdentificationInhabited = false",
    ],
    "NSPeriodicOfficialNormBernsteinAdapter.agda": [
        "concreteBernsteinToOfficialNormIdentification",
        "shellCurlFromConcreteBernstein",
        "vorticityReconstructionFromConcreteLeaves",
    ],
    "NSPeriodicNearTriadCutoffUniformCompletion.agda": [
        "periodicNearTriadCutoffUniformEstimate",
        "nearTriadOfficialUniformInputsInhabited = false",
    ],
    "NSPeriodicFarLowOfficialSchurCompletion.agda": [
        "PeriodicFarLowSchurFactorCoherence",
        "farLowFullSchurIsRowColumnProduct",
        "periodicFarLowOfficialRadiusEightEstimate",
        "farLowOfficialSchurInputsInhabited = false",
    ],
    "NSPeriodicOfficialFarLowSchurAdapter.agda": [
        "factorizedFarLowFromSelectedAuthority",
        "factorizedFarLowSchurCoherence",
        "factorizedFarLowRadiusEightEstimate",
    ],
    "NSPeriodicFarHighTailCompletion.agda": [
        "periodicFarHighOfficialRadiusEightEstimate",
        "farHighOfficialTailInputsInhabited = false",
    ],
    "NSPeriodicOfficialHarmonicAuthorityCompletion.agda": [
        "nearTriadFromSelectedAuthority",
        "farLowFromSelectedAuthority",
        "farHighFromSelectedAuthority",
    ],
    "NSPeriodicWallIHarmonicCompletion.agda": [
        "wallIOfficialNormAdmissibility",
        "wallIFarLowSchurProduct",
        "periodicWallIHarmonicEstimate",
        "wallIOfficialHarmonicInputsInhabited = false",
    ],
    "NSPeriodicIntegratedExpenditureCompletion.agda": [
        "navierStokesDerivativeMeaning",
        "wallIBudgetPaidByCoerciveEnvelope",
        "forcingAndSwitchRemainderMeaning",
        "concretePeriodicNonlinearPaidByEnvelope",
        "periodicIntegratedWeightedShellEstimate",
        "periodicIntegratedVorticityEstimate",
        "periodicIntegratedBKMContinuation",
        "periodicConcreteExpenditureInputsInhabited = false",
    ],
    "NSPeriodicIntegratedExpenditureStandardAdapter.agda": [
        "periodicStandardWeightedShellExpenditure",
        "periodicStandardVorticityExpenditure",
        "periodicStandardBKMContinuation",
    ],
    "NSCompactGammaNormalizedBoundaryInwardnessCompletion.agda": [
        "normalizedAdaptiveCoverageNoFirstExit",
        "normalizedBoundaryPDEInputsInhabited = false",
    ],
    "NSPeriodicAdaptiveSwitchCostCompletion.agda": [
        "adaptiveSwitchingIsControlled",
        "adaptiveTotalSwitchCostBound",
        "adaptiveSwitchCostInputsInhabited = false",
    ],
    "NSPeriodicDiffuseSpectrumBKMCompletion.agda": [
        "periodicDiffuseSpectrumGivesBKM",
        "diffuseSpectrumBKMInputsInhabited = false",
    ],
    "NSPeriodicAllDataCoverageCompletion.agda": [
        "normalizedChartCarriesBothControls",
        "normalizedChartGivesBKM",
        "periodicAllDataVorticityFinite",
        "periodicAllDataContinuesBeyond",
        "allDataAdaptiveCoverageInputsInhabited = false",
    ],
    "NSPeriodicAllDataCutoffCoverageAdapter.agda": [
        "allDataCoverageAtCutoff",
        "Coverage.periodicAllDataVorticityFinite",
    ],
    "NSPeriodicStandardContinuumAdapter.agda": [
        "standardLimitIsLerayHopf",
        "standardCompactGammaCutoffEstimatePasses",
        "standardContinuumBKMContinuation",
    ],
    "NSPeriodicCutoffUniformContinuumBKMCompletion.agda": [
        "FamilyContains",
        "familyMembership",
        "periodicContinuumGlobalRegularity",
        "unconditionalPeriodicGlobalRegularityPromoted = false",
    ],
    "NSPeriodicCutoffUniformContinuumAssembly.agda": [
        "assemblePeriodicCutoffUniformContinuumInputs",
        "Coverage.allDataCoverageAtCutoff",
        "assembledPeriodicContinuumGlobalRegularity",
    ],
    "NSPeriodicOfficialCompletionStatus.agda": [
        "biotSavartTransversalityReductionLevel = machineChecked",
        "strictDissipationMarginReductionLevel = machineChecked",
        "strictMarginExpenditureAdapterStatusLevel = machineChecked",
        "packetFractionQuotientSignReductionLevel = machineChecked",
        "normalizedBoundaryCommonParameterReductionLevel = machineChecked",
        "hysteresisSeparationReductionLevel = machineChecked",
        "adaptiveSwitchSeparationAdapterStatusLevel = machineChecked",
        "diffuseDissipationChargingReductionLevel = machineChecked",
        "diffuseDissipationRouteAdapterStatusLevel = machineChecked",
        "zeroChartDiffuseSelectionReductionLevel = machineChecked",
        "extendedCoverageBKMStatusLevel = machineChecked",
        "weightedEnvelopeLimitTransportReductionLevel = machineChecked",
        "weightedEnvelopeContinuumAdapterStatusLevel = machineChecked",
        "unconditionalPeriodicNavierStokesTheorem = false",
        "clayNavierStokesSubmissionPromoted = false",
    ],
    "NSPeriodicOfficialCompletionRegression.agda": [
        "globalRegularityGateRegression = refl",
        "clayGateRegression = refl",
    ],
    "NSPeriodicSevenAnalyticLeafCutset.agda": [
        "OfficialCarrierAndUniformHarmonicBounds",
        "ConcreteCompactGammaStrictExpenditure",
        "StrictNormalizedBoundarySigns",
        "UniversalSwitchControl",
        "DiffuseSpectrumBKMControl",
        "ExhaustiveZeroChartDiffuseClassification",
        "CutoffUniformBoundAndContinuumTransport",
        "sevenAnalyticLeavesGiveEndpoint",
        "sevenAnalyticLeafObligationsInhabitedInOfficialCarrier = false",
        "sevenAnalyticLeafEndpointPromoted = false",
    ],
    "NSPeriodicBiotSavartTransversality.agda": [
        "biotSavartVelocityIsTransverse",
        "biotSavartTransversalityAssemblyLevel = machineChecked",
    ],
    "NSPeriodicStrictDissipationMargin.agda": [
        "periodicNonlinearComponentsBelowPayments",
        "periodicNonlinearPlusStrictMarginBelowViscosity",
        "periodicNonlinearBelowViscosity",
        "strictDissipationMarginAssemblyLevel = machineChecked",
    ],
    "NSPeriodicIntegratedExpenditureStrictMarginAdapter.agda": [
        "strictMarginPaysOfficialBudget",
        "strictMarginInputsToConcreteExpenditure",
        "strictMarginIntegratedWeightedShellEstimate",
        "strictMarginIntegratedVorticityEstimate",
        "strictMarginIntegratedBKMContinuation",
        "strictMarginExpenditureAdapterLevel = machineChecked",
    ],
    "NSPeriodicPacketFractionQuotientSign.agda": [
        "packetFractionDerivativeStrictlyPositive",
        "packetFractionQuotientSignAssemblyLevel = machineChecked",
    ],
    "NSPeriodicNormalizedBoundaryCommonParameters.agda": [
        "commonParametersToNormalizedBoundaryInputs",
        "commonParameterizedBoundaryHasNoFirstExit",
        "normalizedBoundaryCommonParameterAssemblyLevel = machineChecked",
    ],
    "NSPeriodicHysteresisSeparation.agda": [
        "twoWayHysteresisRequiresDoubleModulus",
        "hysteresisGapExcludesImmediateBackSwitch",
        "hysteresisSeparationAssemblyLevel = machineChecked",
    ],
    "NSPeriodicAdaptiveSwitchSeparationAdapter.agda": [
        "separationExcludesImmediateBackSwitch",
        "switchSeparationToAdaptiveSwitchInputs",
        "adaptiveSwitchControlFromSeparation",
        "adaptiveSwitchSeparationAdapterLevel = machineChecked",
    ],
    "NSPeriodicDiffuseDissipationCharging.agda": [
        "diffuseChargedVorticityBelowTotalBudget",
        "diffuseDissipationChargeGivesFiniteVorticity",
        "diffuseDissipationChargingAssemblyLevel = machineChecked",
    ],
    "NSPeriodicDiffuseDissipationRouteAdapter.agda": [
        "diffuseDissipationRouteToBKMInputs",
        "diffuseDissipationRouteGivesBKM",
        "diffuseDissipationRouteAdapterLevel = machineChecked",
    ],
    "NSPeriodicZeroChartDiffuseSelection.agda": [
        "periodicZeroChartDiffuseSelection",
        "periodicCoverageClassAsDisjunction",
        "zeroChartDiffuseSelectionAssemblyLevel = machineChecked",
    ],
    "NSPeriodicExtendedCoverageBKM.agda": [
        "periodicExtendedCoverageGivesVorticityControl",
        "extendedCoverageBKMAssemblyLevel = machineChecked",
    ],
    "NSPeriodicWeightedEnvelopeLimitTransport.agda": [
        "continuumFullEnvelopeBelowUniformCutoffBound",
        "continuumVorticityBelowUniformCutoffBound",
        "weightedEnvelopeTransportGivesFiniteContinuumVorticity",
        "weightedEnvelopeLimitTransportAssemblyLevel = machineChecked",
    ],
    "NSPeriodicWeightedEnvelopeContinuumAdapter.agda": [
        "weightedEnvelopeVorticityBoundPassesToLimit",
        "weightedEnvelopeContinuumAdapterLevel = machineChecked",
    ],
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "unconditionalPeriodicNavierStokesTheorem = true",
    "clayNavierStokesSubmissionPromoted = true",
    "sevenAnalyticLeafEndpointPromoted = true",
)


def main() -> None:
    errors: list[str] = []
    for name, required in FILES.items():
        path = CLOSURE / name
        if not path.is_file():
            errors.append(f"missing file: {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in required:
            if token not in text:
                errors.append(f"{name}: missing required token {token!r}")
        for token in FORBIDDEN:
            if token in text:
                errors.append(f"{name}: forbidden token {token!r}")

    if errors:
        for error in errors:
            print(f"[error] {error}")
        raise SystemExit(1)

    print(
        "[ok] official periodic norm/expenditure/coverage surface is complete "
        "and fail-closed"
    )


if __name__ == "__main__":
    main()
