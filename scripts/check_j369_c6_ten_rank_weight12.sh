#!/usr/bin/env bash
set -euo pipefail

targets=(
  DASHI/Moonshine/JInvariant369C6TenRankWeightTwelveCrossPollinationExact.agda
  DASHI/Moonshine/JInvariant369CanonicalInterpretationExact.agda
  DASHI/Moonshine/MonsterAtlas6561X8RecognitionObligationExact.agda
  DASHI/Moonshine/JInvariant369NeutralCuspRelationCrossPollinationExact.agda
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
grep -q 'NineBy729BlockRecognition' "${targets[2]}"
grep -q 'Atlas6561X8Recognition' "${targets[2]}"
grep -q 'x8EquivariantRecognitionInhabitedHere' "${targets[2]}"
grep -q 'innerNineToFiveOrbitQuotientIsPaid' "${targets[3]}"
grep -q 'phasePreservingThreeTimesFiveReductionIsPaid' "${targets[3]}"
grep -q 'joinAfterSplit' "${targets[3]}"
grep -q 'distinguishedOrientationDuplicationCollapses' "${targets[3]}"
grep -q 'fourteenIsBalancedRankCarry' "${targets[3]}"
grep -q 'leanEta24NormalizedDeltaSameObjectSourceWritten' "${targets[3]}"
grep -q 'twelvePlusTwelveIsTwentyFour' "${targets[3]}"
grep -q 'finiteZeroPhaseDoesNotEqualCuspVanishing' "${targets[3]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
