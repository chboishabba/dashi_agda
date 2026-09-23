#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Moonshine/JInvariantSheafHyperformAdmissibleDescentExact.agda
ROLLUP=DASHI/JInvariantBase369CrossPollinationEverything.agda

for file in "$OWNER" "$ROLLUP"; do
  [[ -f "$file" ]] || { echo "missing required source: $file" >&2; exit 1; }
done

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'
if grep -nE "$FORBIDDEN_PATTERN" "$OWNER"; then
  echo "forbidden hole, postulate, placeholder, or unsafe option in $OWNER" >&2
  exit 1
fi

grep -q 'PresheafInterface' "$OWNER"
grep -q 'CompatibleOverlap' "$OWNER"
grep -q 'AdmissiblePushoutInterface' "$OWNER"
grep -q 'chosenLocalValueFactorsThroughLocalJ' "$OWNER"
grep -q 'q11CannotFactorThroughLocalJ' "$OWNER"
grep -q 'jLocalCollisionInPullback' "$OWNER"
grep -q 'Base369InteractionPullback' "$OWNER"
grep -q 'base369RelativeFineMustSeparateDistinctStates' "$OWNER"
grep -q 'local27Q11WrongTypeReceipt' "$OWNER"
grep -q 'cardinalityDoesNotCreateAdmissibleGluing' "$OWNER"
grep -q 'literalAnalyticGrothendieckSiteConstructedHere = false' "$OWNER"
grep -q 'jObserverProblem' "$OWNER"
grep -q 'local27CannotBeEligibleForQ11' "$OWNER"
grep -q 'fullFieldRepairIsEligible' "$OWNER"
grep -q 'jRepairTransitionSystem' "$OWNER"
grep -q 'localToFullIsAdmittedStep' "$OWNER"
grep -q 'inverseZetaDivisorBoundary' "$OWNER"
grep -q 'oeisAuditBoundary' "$OWNER"
grep -q 'deltaWeightTwelveBoundary' "$OWNER"
grep -q 'jWeightZeroBoundary' "$OWNER"
grep -q 'leanMirrorReceipt' "$OWNER"
grep -q 'JInvariantSheafHyperformAdmissibleDescentExact' "$ROLLUP"

echo "J/369 sheaf-hyperform descent static guards passed."

scripts/run_agda29_parallel_check.sh   "$OWNER"   "$ROLLUP"
