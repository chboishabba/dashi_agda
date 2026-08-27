#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/FormalClaimTransportGeometryExact.agda
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
  DASHI/Core/FormalizationRecoveryGeometryExact.agda
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
  DASHI/Foundations/WetteArithmeticRepresentationExact.agda
  DASHI/Foundations/WetteConstructiveAutomatonExact.agda
  DASHI/Foundations/WetteArithmeticTransitionBridgeExact.agda
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda
  DASHI/Foundations/WetteRepresentationKernelBridgeExact.agda
  DASHI/Foundations/WetteCertifiedArithmeticKernelExact.agda
  DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
  DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda
  DASHI/Foundations/Wette/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required Wette reconstruction source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# Provenance / promotion-boundary guards.
grep -q 'existenceOfRepresentationMapTransportsEveryClaimIsFalse' \
  DASHI/Core/FormalClaimTransportGeometryExact.agda
grep -q 'comparisonAxesAreDefinitionallyTotallyOrderedIsFalse' \
  DASHI/Core/FormalClaimTransportGeometryExact.agda
grep -q 'arxiv:2508.00459v2' \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
grep -q 'doi:10.3929/ethz-b-000387100' \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
grep -q 'arxiv:1807.05641' \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
grep -q 'provisionalJournalDOIPromotedWithoutVerificationIsFalse' \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
grep -q 'translationAndReconstructionAreSeparateObligationsIsTrue' \
  DASHI/Core/FormalizationRecoveryGeometryExact.agda
grep -q 'sourceLocatedMeansFormalObjectRecoveredIsFalse' \
  DASHI/Core/FormalizationRecoveryGeometryExact.agda
grep -q 'relativeCompletenessIsDefinitionallyNextLinearLevelIsFalse' \
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda
grep -q 'proofTranslationCoordinateImpliesSemanticSoundnessCoordinateIsFalse' \
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda
grep -q 'doi:10.1007/978-3-642-86745-3_9' \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'doi:10.2307/2272630' \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'secondaryReportedJSLItemsPromotedToPrimaryWithoutCheckIsFalse' \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'unverified1974DOIFabricatedIsFalse' \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'relativeCompletenessShouldBeDefinedBeforeSourceRecoveryIsFalse' \
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda
grep -q 'sourceExtractionPrecedesTheoremDischargeIsTrue' \
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda
grep -q 'bibliographicLocationIsNotPrimaryTextInspectionIsTrue' \
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
grep -q 'calibrationLiteratureReplacesWettePrimarySourcesIsFalse' \
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
grep -q 'historicalWetteCodecRecoveredIsFalse' \
  DASHI/Foundations/WetteArithmeticRepresentationExact.agda
grep -q 'fractranMachineIsHistoricalWetteMachineIsFalse' \
  DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
grep -q 'ordinaryArithmeticInconsistencyEstablishedIsFalse' \
  DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
grep -q 'machineReachabilityIsAlreadyMetatheoreticContradictionIsFalse' \
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
grep -q 'translatedContradictionProofIsAlreadySemanticAbsurdityIsFalse' \
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda
grep -q 'historicalWetteComparisonArithmeticBridgeRecoveredIsFalse' \
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda
grep -q 'theoremProvesOrdinaryArithmeticConsistencyIsFalse' \
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
grep -q 'historicalWetteToOrdinaryArithmeticTranslationRecoveredIsFalse' \
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
grep -q 'historicalWetteOrdinaryArithmeticEquiconsistencyRecoveredIsFalse' \
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda
grep -q 'contradictionInOrdinaryArithmeticProvedIsFalse' \
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/FormalClaimTransportGeometryExact.agda \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda \
  DASHI/Core/FormalizationRecoveryGeometryExact.agda \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda \
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda \
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda \
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda \
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda \
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda \
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda \
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda \
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda \
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda \
  DASHI/Foundations/Wette/Everything.agda
