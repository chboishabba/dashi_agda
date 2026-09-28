#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Cognition/PNF/EditTransportLeafLocalityExact.agda
  DASHI/Cognition/PNF/IndependentFibreBatchExecutionExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerRegression.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda
  DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
  DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
  DASHI/Cognition/PNF/SensibLawScale1ExactReplayEconomyReceipt.agda
  DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda
)

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing SCALE-1.P Agda source: $file" >&2; exit 1; }
  if grep -nE '\b(postulate|{-# *TERMINATING *#}|{-# *NON_TERMINATING *#})\b' "$file"; then
    echo "forbidden proof escape found in $file" >&2
    exit 1
  fi
done

agda DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerExact.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerRegression.agda
agda DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
agda DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
agda DASHI/Cognition/PNF/SensibLawScale1ExactReplayEconomyReceipt.agda
agda DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda

grep -q 'verifiedLocalityDoesNotImplyFewCommitBarriers'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'fewCommitBarriersDoNotProveSemanticIndependence'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'storageSyncLatencyDoesNotBecomeSemanticRecomputation'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'fixtureBatchedAuthorityMatchesSequential'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda
grep -q 'reviewProjectionCacheMustTrackInputFingerprint'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionCacheMustTrackConsumerScope'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionCacheMustTrackOccurrenceAncestry'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionWallAloneCannotProveParserDominance'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionV2CacheMustTrackParserRun'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionV2CacheMustTrackReconciliationDetector'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewProjectionV2ExactReuseDoesNotRescanOccurrences'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'fixtureV2ReusePerformsNoOccurrenceLookup'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
grep -q 'broadReviewFallbackDoesNotProveIncrementalEconomy'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'reviewDeltaReceiptDoesNotCreateSemanticAuthority'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyExact.agda
grep -q 'fixtureDeltaReviewUsesExactChangedFibreSet'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
grep -q 'fixtureDeltaReviewActuallyUsesDeltaInput'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
grep -q 'fixtureReuseDoesNotRecomputeReviewCandidates'   DASHI/Cognition/PNF/SensibLawReviewProjectionEconomyRegression.agda
grep -q 'exactReplayCannotCertifyFreshParserDominance'   DASHI/Cognition/PNF/SensibLawScale1ExactReplayEconomyReceipt.agda
grep -q 'exactReplayCandidatePathUsesNoCommitBarrier'   DASHI/Cognition/PNF/SensibLawScale1ExactReplayEconomyReceipt.agda

echo 'SCALE-1.P locality/commit/review-projection economy Agda checks passed'
