#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Analysis/RiemannAristotlePoleQuotientComplementMarginCompilerExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientBidiMeetingExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientSplitComplementBudgetExact.agda
  DASHI/Analysis/RiemannAristotleRankTwoPoleQuotientLaneSeparationExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientGammaBudgetTargetExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientClusterMarginTargetExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientCurrentCutExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientCurrentCutRegression.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  agda DASHI/Analysis/RiemannAristotlePoleQuotientComplementMarginCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientSplitComplementBudgetExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientBidiMeetingExact.agda
  agda DASHI/Analysis/RiemannAristotleRankTwoPoleQuotientLaneSeparationExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientGammaBudgetTargetExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientClusterMarginTargetExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientCurrentCutRegression.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
