#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
FILES=(
  DASHI/Analysis/RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda
  DASHI/Analysis/RiemannAristotleFiniteNearCoreSchurCompilerExact.agda
  DASHI/Analysis/RiemannAristotleDeterministicProjectiveSchurReturnExact.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierExact.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
)
for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done
if command -v agda >/dev/null 2>&1; then
  agda DASHI/Analysis/RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleFiniteNearCoreSchurCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleDeterministicProjectiveSchurReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
