#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
trace_owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistCompositeReferenceTraceExact.agda"
round_owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound10CompositeTraceProgressExact.agda"
py_trace="$root/scripts/twenty_scientist_composite_reference_trace.py"
aggregate="$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

for file in "$trace_owner" "$round_owner" "$py_trace"; do
  test -f "$file"
done

grep -q 'ungatedCompositeTraceCount = 2' "$trace_owner"
grep -q 'longDurationCompositeTrace' "$trace_owner"
grep -q 'autonomousSurveyCompositeTrace' "$trace_owner"
grep -q 'traceRanksSoftResiduals = true' "$trace_owner"
grep -q 'traceExecutionDoesNotPayQualification = false' "$trace_owner"
grep -q 'traceExecutionDoesNotPayHistoricalDeployment = false' "$trace_owner"

grep -q 'SOFT_RESIDUAL_WEIGHTS = {' "$py_trace"
grep -q 'def trace_for' "$py_trace"
grep -q '"historical_deployment_paid": False' "$py_trace"
grep -q '"operational_qualification_paid": False' "$py_trace"
grep -q '"source_replication_paid": False' "$py_trace"

grep -q 'round10ScientificCohortCount = 20' "$round_owner"
grep -q 'round10EveryScientistTouched = true' "$round_owner"
grep -q 'round10UngatedCompositeCount = 2' "$round_owner"
grep -q 'round10HardGatedCompositeCount = 2' "$round_owner"
grep -q 'round10TraceDoesNotPayHistoricalUse = false' "$round_owner"

for person in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$person" "$round_owner"
done

grep -q 'MissingDeceasedTwentyScientistCompositeReferenceTraceExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistRound10CompositeTraceProgressExact' "$aggregate"

echo 'Round-10 composite reference trace static contract: OK'
