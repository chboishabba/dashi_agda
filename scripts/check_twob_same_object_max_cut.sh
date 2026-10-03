#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BM22RuntimeMaxCutReceiptExact.agda
  DASHI/Moonshine/OggSSP2BIntegralMoonshineLocalActionSourceExact.agda
  DASHI/Moonshine/OggSSP2BBinaryTetrahedralDefectSourceExact.agda
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

grep -q 'externalRestrictedLocalActionIsSourced' "${targets[1]}"
grep -q 'repoSameObjectTateCarrierWeldStillOpen' "${targets[1]}"
grep -q 'sourcedExistenceDoesNotConstructFormalTateCarrierWeld' "${targets[1]}"

grep -q 'centralizerTwoAdicFactorization' "${targets[2]}"
grep -q 'defectIdentityIsThree' "${targets[2]}"
grep -q 'defectMinusOneIsThree' "${targets[2]}"
grep -q 'defectOrderFourIsTwo' "${targets[2]}"
grep -q 'defectOrderThreeIsOne' "${targets[2]}"
grep -q 'defectOrderSixIsOne' "${targets[2]}"
grep -q 'matchingNumbersDoNotConstructModeRecognition' "${targets[2]}"

grep -q 'externalIntegralLocalActionSourced' "${targets[3]}"
grep -q 'tenDimensionalFactorMultiplicityIsTen' "${targets[3]}"
grep -q 'bareM22CompletionRouteKilled' "${targets[3]}"
grep -q 'formalIntegralTateCarrierWeldStillOpen' "${targets[3]}"
grep -q 'actualTenSubquotientStillOpen' "${targets[3]}"
grep -q 'largerCompletionActionStillOpen' "${targets[3]}"
grep -q 'actualModeDefectRecognitionStillOpen' "${targets[3]}"
grep -q 'thirtyToP31StillObserverOnly' "${targets[3]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
