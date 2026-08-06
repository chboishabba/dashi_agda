#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Closure/NSTriadKNProjectedConvectionEnergyFluxExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoExactFluxKernelDecompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact.agda
  DASHI/Physics/Closure/NSTriadKNIntegerFourierModeAddExact.agda
  DASHI/Physics/Closure/NSTriadKNComplexCommutativeRingExact.agda
  DASHI/Physics/Closure/NSTriadKNRationalLerayProjectionExact.agda
  DASHI/Physics/Closure/NSTriadKNRationalLeraySelfAdjointExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBernsteinExponentCalibrationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIncrementTensorPolarizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIncrementKernelFourierMultiplierExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCharacterWeightedIncrementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCharacterMultiplierBridgeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLinearIntegralWeightedIncrementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteLinearIntegralRealizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoComplexLinearIntegralWeightedIncrementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteComplexWeightedIncrementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicComplexCharacterMultiplierExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicComplexMultiplierCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTranslationTensorConvolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteComplexTranslationTensorConvolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteResonantPairFoldExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteComplexResonantPairFoldExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedIncrementFubiniExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteComplexFubiniExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteThreePairCoefficientExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreeWayPairPartitionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSignedConvolutionYoungExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalYoungSameConstantExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJensenSquareExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNormalizedWeightedJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicHalfSplitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSourceFaithfulSection4Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedSourceSection4Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSourceJ11J12ProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedSourceJ11J12ProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSection4TerminalYoungClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDiscreteCutoffEnergyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDiscreteTerminalCutoffExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDiscreteGronwallExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformGronwallExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteMeanValueSelectionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteMeanValueGronwallExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSchurEnvelopeRefinementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePointwiseSchurFactorizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePhysicalSchurSummationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourInteractionSchurBoundsExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourInteractionFactorizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourInteractionSquaredConvolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCutoffSection4RecursionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSmallGradientAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteAbsorbedBlockRecursionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourAlignedShellSummabilityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBlockDecayToFourShellSummabilityExact.agda
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
  DASHI/Physics/Closure/NSTriadKNLuoNoCircularityAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompleteSubmissionCompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompleteSubmissionFrontierReceipt.agda

  DASHI/Physics/Closure/NSTriadKNLuoLemmaFamilyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFullCompletionLemmaInventoryExact.agda

  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaFiniteFourierFoundationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaCriticalCutsetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaPathCompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaFrontierReceipt.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticFrontierValidation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe' "$file"; then
    echo "forbidden hole, postulate, unsolved-meta option, or unsafe option in $file" >&2
    exit 1
  fi
done

python3 scripts/check_ns_luo_full_lemma_inventory.py
python3 scripts/check_ns_luo_highest_alpha_path.py
bash scripts/check_ns_luo_submission_audit.sh

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticFrontierValidation.agda
