#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BTate276M24BrauerRuntimeReceiptExact.agda
  DASHI/Moonshine/OggSSP2BDefectTwoBitProvenanceSelectorExact.agda
  DASHI/Moonshine/OggSSP2BDefectProvenanceSearchNoGoExact.agda
  DASHI/Moonshine/OggSSP2BMonster2LocalThree276SourceExact.agda
  DASHI/Moonshine/OggSSP2BPostBrauerOuterActionBlindSpotExact.agda
  DASHI/Moonshine/OggSSP2BPostBrauerSameObjectFrontierExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

grep -q 'allBrauerRowsMatchIsTrue' "${targets[0]}"
grep -q 'semisimplifiedIngressIsPaid' "${targets[0]}"
grep -q 'literalModuleIsomorphismStillOpen' "${targets[0]}"
grep -q 'explicitQ10StillOpen' "${targets[0]}"

grep -q 'provenanceChoiceCountIsFour' "${targets[1]}"
grep -q 'orderFourIsForced' "${targets[1]}"
grep -q 'defectProfileDoesNotConstructTwoProvenanceBits' "${targets[1]}"

grep -q 'remainingSourceDecisionCountIsTwo' "${targets[2]}"
grep -q 'orientedRouteDoesNotSourceSelectBits' "${targets[2]}"
grep -q 'galoisRouteDoesNotSourceSelectBits' "${targets[2]}"
grep -q 'provenanceChoiceCountStillFour' "${targets[2]}"

grep -q 'three276SourcePaid' "${targets[3]}"
grep -q 'trialitySourcePaid' "${targets[3]}"
grep -q 'characteristicTwoTateIdentificationStillOpen' "${targets[3]}"

grep -q 'brauerIngressPaid' "${targets[4]}"
grep -q 'finiteOuterSourceFound' "${targets[4]}"
grep -q 'brauerPassDoesNotDetermineOuterJ2x5Action' "${targets[4]}"

grep -q 'brauerAllRowsMatch' "${targets[5]}"
grep -q 'semisimplifiedIngressReceiptPaid' "${targets[5]}"
grep -q 'outerJ2x5MatchesTwo' "${targets[5]}"
grep -q 'remainingDefectSourceDecisionCountIsTwo' "${targets[5]}"
grep -q 'nineOrbitIndexingIsNotSemanticIdentity' "${targets[5]}"
grep -q 'actualOuterActionOnSameQStillOpen' "${targets[5]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
