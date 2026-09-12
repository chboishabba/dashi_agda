#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"

kernel="$root/DASHI/Culture/MissingDeceasedTwentyScientistScienceExecutionKernelExact.agda"
round="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound12ScienceImplementationProgressExact.agda"
coverage="$root/DASHI/Culture/MissingDeceasedTwentyScientistScienceImplementationCoverageExact.agda"
aggregate="$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

for f in "$kernel" "$round" "$coverage"; do test -f "$f"; done

grep -q 'scienceExecutionKernelsCount = 20' "$kernel"
grep -q 'scienceRunnableCount = 18' "$kernel"
grep -q 'scienceSourceReplayReadyCount = 7' "$kernel"
grep -q 'scienceGatedCount = 2' "$kernel"
grep -q 'scienceExecutionDoesNotPayHistoricalUse = false' "$kernel"
grep -q 'scienceExecutionDoesNotPayCustody = false' "$kernel"

grep -q 'round12ScientificCohortCount = 20' "$round"
grep -q 'round12EveryScientistTouched = true' "$round"
grep -q 'round12ScienceOnlyFocus = true' "$round"
grep -q 'round12ScienceRunnableCount = 18' "$round"

grep -q 'leblancCoverage.*finiteWitness' "$coverage" || grep -A5 -q 'leblancCoverage' "$coverage"
grep -q 'hicksCoverage' "$coverage"
grep -q 'ningCoverage' "$coverage"
grep -q 'chenCoverage' "$coverage"
grep -q 'zhangXiaoxinCoverage' "$coverage"
grep -q 'fangCoverage' "$coverage"
grep -q 'yanCoverage' "$coverage"

grep -q 'MissingDeceasedTwentyScientistScienceExecutionKernelExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistRound12ScienceImplementationProgressExact' "$aggregate"

echo 'Round-12 science execution kernel static contract: OK'
