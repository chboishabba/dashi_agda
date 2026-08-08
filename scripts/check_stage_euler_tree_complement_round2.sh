#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

POINTED_BULK_SKIP_BASE=1 bash scripts/check_pointed_bulk_sporadic_tarot.sh

sources=(
  DASHI/Foundations/BalancedTernaryResidualTreeExact.agda
  DASHI/Foundations/StageProfile369SignedDistanceExact.agda
  DASHI/Foundations/ConstrainedFrameEulerSelectorExact.agda
  DASHI/Moonshine/DepthTwoNonaryStageTenComplementExact.agda
  DASHI/Biology/StageEulerTreeComplementRound2Validation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'stageFiveRetainedTree'
  'stageFiveProjectionDoesNotEraseTwo'
  'stageFiveDecisionSignature'
  'stageSixDualSignature'
  'nonaryDepthTwoIsTenPlusSeventyOne'
  'seventyOneMatchesExistingOggLane'
  'invariantCarrierComplementConstructedIsFalse'
  'frameConstrainedMinimum'
  'finiteEulerStationarity'
  'localMinimumProvesUniversalTruthIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

if command -v agda >/dev/null 2>&1; then
  agda -i . -l standard-library \
    DASHI/Biology/StageEulerTreeComplementRound2Validation.agda
else
  echo "agda unavailable: skipped kernel check" >&2
fi
