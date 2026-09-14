#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"

required=(
  "DASHI/Culture/MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact.agda"
)
for f in "${required[@]}"; do test -f "$root/$f"; done

grep -q 'round19ScientificCohortCount = 20' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact.agda"
grep -q 'round19EveryScientistTouched = true' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact.agda"
grep -q 'round19CrossPollinationPromotionCount = 6' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact.agda"
grep -q 'crossPollinationBindingsCount = 6' "$root/DASHI/Culture/MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact.agda"
grep -q 'crossPollinationDoesNotPayHistoricalDeployment = false' "$root/DASHI/Culture/MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact.agda"
grep -q 'crossPollinationDoesNotPayCommonProgramme = false' "$root/DASHI/Culture/MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact.agda"
grep -q 'crossPollinationDoesNotPayCustody = false' "$root/DASHI/Culture/MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-19 cross-pollination Pareto static contract: OK'
