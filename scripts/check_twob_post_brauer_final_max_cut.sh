#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BTate276M24BrauerRuntimeReceiptExact.agda
  DASHI/Moonshine/OggSSP2BDefectTwoBitProvenanceSelectorExact.agda
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

grep -q 'three276SourcePaid' "${targets[2]}"
grep -q 'trialitySourcePaid' "${targets[2]}"
grep -q 'characteristicTwoTateIdentificationStillOpen' "${targets[2]}"

grep -q 'brauerIngressPaid' "${targets[3]}"
grep -q 'finiteOuterSourceFound' "${targets[3]}"
grep -q 'brauerPassDoesNotDetermineOuterJ2x5Action' "${targets[3]}"

grep -q 'brauerAllRowsMatch' "${targets[4]}"
grep -q 'semisimplifiedIngressPaid' "${targets[4]}"
grep -q 'outerJ2x5MatchesTwo' "${targets[4]}"
grep -q 'remainingDefectSourceDecisionCountIsTwo' "${targets[4]}"
grep -q 'nineOrbitIndexingIsNotSemanticIdentity' "${targets[4]}"
grep -q 'actualOuterActionOnSameQStillOpen' "${targets[4]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
