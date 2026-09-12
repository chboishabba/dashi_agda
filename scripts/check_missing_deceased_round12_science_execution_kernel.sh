#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"

kernel="$root/DASHI/Culture/MissingDeceasedTwentyScientistScienceExecutionKernelExact.agda"
round="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound12ScienceImplementationProgressExact.agda"
coverage="$root/DASHI/Culture/MissingDeceasedTwentyScientistScienceImplementationCoverageExact.agda"
aggregate="$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
leblanc_numeric="$root/DASHI/Physics/Nuclear/LeBlancFSPICNumericEnvelopeExact.agda"
reza_arithmetic="$root/DASHI/Physics/Materials/RezaBurnResistantAlloyCompositionTradeoffExact.agda"
zhang_arithmetic="$root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastRecallArithmeticExact.agda"

for f in "$kernel" "$round" "$coverage" "$leblanc_numeric" "$reza_arithmetic" "$zhang_arithmetic"; do test -f "$f"; done

grep -q 'scienceExecutionKernelsCount = 20' "$kernel"
grep -q 'scienceRunnableCount = 18' "$kernel"
grep -q 'scienceSourceReplayReadyCount = 7' "$kernel"
grep -q 'scienceGatedCount = 2' "$kernel"
grep -q 'scienceExecutionDoesNotPayHistoricalUse = false' "$kernel"
grep -q 'scienceExecutionDoesNotPayCustody = false' "$kernel"

grep -q 'round12ScientificCohortCount = 20' "$round"
grep -q 'round12EveryScientistTouched = true' "$round"
grep -q 'round12ScienceOnlyFocus = true' "$round"
grep -q 'round12NewScienceArithmeticOwnerCount = 3' "$round"

grep -q 'pressureSpanCloses = refl' "$leblanc_numeric"
grep -q 'massFlowSpanCloses = refl' "$leblanc_numeric"
grep -q 'example1CompositionCloses = refl' "$reza_arithmetic"
grep -q 'example2CompositionCloses = refl' "$reza_arithmetic"
grep -q 'lowerRecallBracketCloses = refl' "$zhang_arithmetic"
grep -q 'upperRecallBracketCloses = refl' "$zhang_arithmetic"

grep -q 'finiteOrStrongerCoverageCount = 18' "$coverage"
grep -q 'leblancCoverage' "$coverage"
grep -q 'hicksCoverage' "$coverage"
grep -q 'ningCoverage' "$coverage"
grep -q 'chenCoverage' "$coverage"
grep -q 'zhangXiaoxinCoverage' "$coverage"
grep -q 'fangCoverage' "$coverage"
grep -q 'yanCoverage' "$coverage"

grep -q 'MissingDeceasedTwentyScientistScienceExecutionKernelExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistRound12ScienceImplementationProgressExact' "$aggregate"
grep -q 'LeBlancFSPICNumericEnvelopeExact' "$aggregate"
grep -q 'RezaBurnResistantAlloyCompositionTradeoffExact' "$aggregate"
grep -q 'ZhangXiaoxinForecastRecallArithmeticExact' "$aggregate"

echo 'Round-12 science execution kernel static contract: OK'
