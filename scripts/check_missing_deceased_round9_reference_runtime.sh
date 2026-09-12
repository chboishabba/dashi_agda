#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
runtime_owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact.agda"
round_owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound9ReferenceRuntimeProgressExact.agda"
py_runtime="$root/scripts/twenty_scientist_embodied_reference_runtime.py"
aggregate="$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

for file in "$runtime_owner" "$round_owner" "$py_runtime"; do
  test -f "$file"
done

grep -q 'referenceRuntimeSlotsCount = 20' "$runtime_owner"
grep -q 'referenceRunnableSlotCount = 18' "$runtime_owner"
grep -q 'referenceGatedSlotCount = 2' "$runtime_owner"
grep -q 'referencePlanFor' "$runtime_owner"
grep -q 'referenceRuntimeDefinesFormalSemantics = false' "$runtime_owner"
grep -q 'referenceRuntimePaysHistoricalDeployment = false' "$runtime_owner"
grep -q 'referenceRuntimeCanEmitReverseAcquisitionPlan = true' "$runtime_owner"

grep -q 'SLOTS = {' "$py_runtime"
grep -q 'APPLICATIONS = {' "$py_runtime"
grep -q '"historical_deployment_paid": False' "$py_runtime"
grep -q '"formal_semantics_defined": False' "$py_runtime"
grep -q 'def plan_for' "$py_runtime"

grep -q 'round9ScientificCohortCount = 20' "$round_owner"
grep -q 'round9EveryScientistTouched = true' "$round_owner"
grep -q 'round9ReferenceRunnableCount = 18' "$round_owner"
grep -q 'round9GatedCount = 2' "$round_owner"
grep -q 'runtimeExecutionDoesNotPaySourceReplay = false' "$round_owner"
grep -q 'runtimeExecutionDoesNotPayHistoricalUse = false' "$round_owner"

for person in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$person" "$round_owner"
done

grep -q 'MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistRound9ReferenceRuntimeProgressExact' "$aggregate"

echo 'Round-9 reference-runtime static contract: OK'
