#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
  DASHI/Analysis/RiemannReflectionPairBlockExact.agda
  DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
  DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
  DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
  DASHI/Analysis/ZetaTheoremSurface.agda
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi

  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

orbit=DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
pair=DASHI/Analysis/RiemannReflectionPairBlockExact.agda
hyper=DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
c3=DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
regression=DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
surface=DASHI/Analysis/ZetaTheoremSurface.agda
aggregate=DASHI/EverythingRiemannReflectionOrbitDefect2026.agda

require_pattern "$orbit" 'reflectInvolutive'
require_pattern "$orbit" 'reflectionFixedImpliesCriticalCentre'
require_pattern "$orbit" 'squaredDefectReflectionInvariant'
require_pattern "$orbit" 'zeroDefectImpliesCriticalCentre'
require_pattern "$orbit" 'leftRightCountsEqual'
require_pattern "$orbit" 'nonFixedSplitsIntoEqualSides'
require_pattern "$pair" 'reflectionBlockTraceAlwaysZero'
require_pattern "$pair" 'reflectionBlockDeterminantMagnitudeIsSquaredDefect'
require_pattern "$pair" 'nearAndFarTraceCollide'
require_pattern "$hyper" 'sourcePositiveIndexBudget'
require_pattern "$hyper" 'offLineCountIsTwoSourcePositiveBudgets'
require_pattern "$hyper" 'sourceSignatureCannotDetermineSquaredDefect'
require_pattern "$hyper" 'DistanceSensitiveOffLineAdapter'
require_pattern "$c3" 'completePhaseOrbitCancels'
require_pattern "$c3" 'c3OrbitRoleInversionInvariant'
require_pattern "$c3" 'zetaSameRoleCanRetainDifferentDefects'
require_pattern "$regression" 'regressionSignatureCannotRecoverDefect'
require_pattern "$surface" 'RiemannWeilOffLineHyperbolicBlockExact'
require_pattern "$aggregate" 'RiemannReflectionOrbitDefectRegression'

scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda \
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
