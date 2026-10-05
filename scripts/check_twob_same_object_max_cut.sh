#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BM22RuntimeMaxCutReceiptExact.agda
  DASHI/Moonshine/OggSSP2BM22d2Completion10RuntimeReceiptExact.agda
  DASHI/Moonshine/OggSSP2BIntegralMoonshineLocalActionSourceExact.agda
  DASHI/Moonshine/OggSSP2BBinaryTetrahedralDefectSourceExact.agda
  DASHI/Moonshine/OggSSP2BTateGradingConventionBridgeExact.agda
  DASHI/Moonshine/OggSSP2BSameObjectMaxCutFrontierExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

grep -q 'runtimeRestrictedDimensionCloses276' "${targets[0]}"
grep -q 'totalTenDimensionalFactorMultiplicityIsTen' "${targets[0]}"
grep -q 'bareM22InvolutionDoesNotRealizeCompletionFivePairs' "${targets[0]}"
grep -q 'runtimeTenAIdentification' "${targets[0]}"
grep -q 'runtimeTenBIdentification' "${targets[0]}"

grep -q 'outerJ2x5MatchCountIsTwo' "${targets[1]}"
grep -q 'tenAOuterCompletionCandidate' "${targets[1]}"
grep -q 'tenBOuterCompletionCandidate' "${targets[1]}"
grep -q 'outerCompletionCandidateDoesNotIdentifyActualTateAction' "${targets[1]}"
grep -q 'actualTwoBTateSubquotientIdentifiedIsFalse' "${targets[1]}"

grep -q 'externalRestrictedLocalActionIsSourced' "${targets[2]}"
grep -q 'repoSameObjectTateCarrierWeldStillOpen' "${targets[2]}"
grep -q 'sourcedExistenceDoesNotConstructFormalTateCarrierWeld' "${targets[2]}"

grep -q 'centralizerTwoAdicFactorization' "${targets[3]}"
grep -q 'defectIdentityIsThree' "${targets[3]}"
grep -q 'defectMinusOneIsThree' "${targets[3]}"
grep -q 'defectOrderFourIsTwo' "${targets[3]}"
grep -q 'defectOrderThreeIsOne' "${targets[3]}"
grep -q 'defectOrderSixIsOne' "${targets[3]}"
grep -q 'matchingNumbersDoNotConstructModeRecognition' "${targets[3]}"

grep -q 'apparentParityConflictResolved' "${targets[4]}"
grep -q 'currentWeightTwoH0OrientationRetained' "${targets[4]}"
grep -q 'currentWeightThreeH1OrientationRetained' "${targets[4]}"
grep -q 'parityConventionShiftIsRequired' "${targets[4]}"

grep -q 'externalIntegralLocalActionSourced' "${targets[5]}"
grep -q 'tenDimensionalFactorMultiplicityIsTen' "${targets[5]}"
grep -q 'bareM22CompletionRouteKilled' "${targets[5]}"
grep -q 'm22d2FiniteCompletionPhaseObserved' "${targets[5]}"
grep -q 'm22d2OuterFivePairBasisVerified' "${targets[5]}"
grep -q 'formalIntegralTateCarrierWeldStillOpen' "${targets[5]}"
grep -q 'actualTenSubquotientStillOpen' "${targets[5]}"
grep -q 'actualTateCompletionActionStillOpen' "${targets[5]}"
grep -q 'actualModeDefectRecognitionStillOpen' "${targets[5]}"
grep -q 'thirtyToP31StillObserverOnly' "${targets[5]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
