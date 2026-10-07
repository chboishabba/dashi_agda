#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BTate276M24BrauerRuntimeReceiptExact.agda
  DASHI/Moonshine/OggSSP2BDefectTwoBitProvenanceSelectorExact.agda
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

grep -q 'brauerAllRowsMatch' "${targets[2]}"
grep -q 'semisimplifiedIngressPaid' "${targets[2]}"
grep -q 'outerJ2x5MatchesTwo' "${targets[2]}"
grep -q 'remainingDefectSourceDecisionCountIsTwo' "${targets[2]}"
grep -q 'nineOrbitIndexingIsNotSemanticIdentity' "${targets[2]}"
grep -q 'actualOuterActionOnSameQStillOpen' "${targets[2]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
