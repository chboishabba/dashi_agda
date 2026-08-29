#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
  DASHI/Analysis/RiemannAristotleSharedWindowCertificateExact.agda
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnExact.agda
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierExact.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
  DASHI/Analysis/RiemannAristotleABCDECompilerExact.agda
  DASHI/Analysis/RiemannAristotleABCDECompilerRegression.agda
  DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundary.agda
  DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundaryRegression.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  agda DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
  agda DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  agda DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
  agda DASHI/Analysis/RiemannAristotleABCDECompilerRegression.agda
  agda DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundaryRegression.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
