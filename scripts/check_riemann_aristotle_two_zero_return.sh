#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnExact.agda
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  agda DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  agda DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
