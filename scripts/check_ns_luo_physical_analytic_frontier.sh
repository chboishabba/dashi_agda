#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Closure/NSTriadKNProjectedConvectionEnergyFluxExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoExactFluxKernelDecompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIncrementTensorPolarizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIncrementKernelFourierMultiplierExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSignedConvolutionYoungExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicMultiplierRealizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPointwisePairFoldReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCanonicalSourceSchurIdentificationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoEquation42PhysicalIdentityAdapterExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoOfficialPerModeShellMeaningExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSection4PhysicalBoundsAdapterExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFixedShiftRecursionReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoOfficialFixedShiftCoreExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoProjectedConvectionOfficialParsevalUpgradeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCutoffEnergyOfficialUpgradeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCanonicalAnalyticInputsBuilderExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoMaximalTimeGlobalizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticTaskLedger.agda
  DASHI/Physics/Closure/NSTriadKNLuoCanonicalAnalyticFrontierReceipt.agda

  DASHI/Physics/Closure/NSTriadKNLuoWeightedIncrementFourierIntegrationCutsetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreePairCoefficientCutsetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoMultiplierReceiptAndSourceSchurCutsetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAnalyticFractionalPowerIdentificationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoMeanValueGronwallReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalBlockDecayReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteInfiniteRealPromotionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSubmissionDependencyCutsetExact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicNavierStokesSubmissionTheoremExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGlobalPhysicalSolutionReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSubmissionAuditReceiptExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCoreSourceFidelityInventoryExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSubmissionLemmaCrosswalkExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalPathCompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompleteSubmissionCompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompleteSubmissionFrontierReceipt.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticFrontierValidation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|\?($|[^[:alnum:]_])|^[[:space:]]*postulate([[:space:]]|$)' "$file"; then
    echo "forbidden hole, metavariable marker, or postulate in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticFrontierValidation.agda
