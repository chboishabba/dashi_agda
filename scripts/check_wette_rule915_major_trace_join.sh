#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969CertifiedTraceWeakeningExact.agda
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette major-trace join source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'entireCertifiedTracesReplayUnderContextExtensionIsTrue' \
  DASHI/Foundations/Wette1969CertifiedTraceWeakeningExact.agda
grep -q 'replayChangesHistoricalRuleBodiesIsFalse' \
  DASHI/Foundations/Wette1969CertifiedTraceWeakeningExact.agda

grep -q 'premise18And27TracesMayStartIndependentlyFromSameScaffoldIsTrue' \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
grep -q 'secondMajorTraceReplaysOverFirstWithoutChangingRuleBodiesIsTrue' \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
grep -q 'joinedTargetContainsBothMajorProofsIsTrue' \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
grep -q 'generatedScaffoldPersistsToJoinedMajorTargetIsTrue' \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
grep -q 'replayManufacturesEitherMajorProofWithoutItsOriginalTraceIsFalse' \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969CertifiedTraceWeakeningExact.agda \
  DASHI/Foundations/Wette1969Rule915IndependentMajorTraceJoinExact.agda
