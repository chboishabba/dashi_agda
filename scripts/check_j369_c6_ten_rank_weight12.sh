#!/usr/bin/env bash
set -euo pipefail

targets=(
  DASHI/Moonshine/JInvariant369C6TenRankWeightTwelveCrossPollinationExact.agda
  DASHI/Moonshine/JInvariant369CanonicalInterpretationExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

grep -q 'smithHalfTurnCommutesWithModularReflection' "${targets[0]}"
grep -q 'rank14IsRank13PlusOne' "${targets[0]}"
grep -q 'twelveSquaredIs144' "${targets[0]}"
grep -q 'twelveCubedIs1728' "${targets[0]}"
grep -q 'signedMagnitudeStillCannotFactorThroughCoarseLevel3' "${targets[0]}"
grep -q 'signedMagnitudeDoesNotFactorThroughLevel3' "${targets[1]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
