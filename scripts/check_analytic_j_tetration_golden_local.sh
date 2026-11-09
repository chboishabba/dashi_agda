#!/usr/bin/env bash
# Exact-head local Agda 2.9 acceptance: no CI and no success if checker absent.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/AbelSchroederLogCocycleTransportExact.agda
  DASHI/Moonshine/AbelBishopKoenigsComponentwiseCompletionExact.agda
  DASHI/Moonshine/AbelBishopKoenigsIncrementSeriesExact.agda
  DASHI/Moonshine/AbelBishopKoenigsFiniteTelescopingExact.agda
  DASHI/Moonshine/AbelBishopKoenigsGeometricAbsoluteExact.agda
  DASHI/Moonshine/AbelBishopKoenigsTrajectoryDifferenceLimitExact.agda
  DASHI/Moonshine/AbelBishopOriginalComplexCarrierWeldExact.agda
  DASHI/Moonshine/AbelBishopOriginalExponentialIteratesExact.agda
  DASHI/Moonshine/AbelBishopOriginalQParameterExact.agda
  DASHI/Moonshine/AbelBishopRound11QPeriodInstanceExact.agda
  DASHI/Moonshine/AbelE8RootE4FirstCoefficientExact.agda
  DASHI/Moonshine/AbelE8RootTriadic243CountComparisonExact.agda
  DASHI/Moonshine/AbelE8GeneratedRootNormTwoExact.agda
  DASHI/Moonshine/AbelE8ThetaParityProjectorExact.agda
  DASHI/Moonshine/AbelE8HalfOddShellInvolutionExact.agda
  DASHI/Moonshine/AbelBishopMachinQuarterToQPeriodExact.agda
  DASHI/Moonshine/AbelBishopQSeriesSetoidPeriodTransportExact.agda
  DASHI/Moonshine/AbelOriginalMovingLevelObserverTransportExact.agda
  DASHI/Moonshine/AbelCarrierFixedLocusTransportExact.agda
)

if command -v git >/dev/null 2>&1; then
  echo "HEAD: $(git rev-parse HEAD)"
  if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "WARNING: worktree dirty; exact-head receipt requires recording diff" >&2
  fi
fi

for target in "${targets[@]}"; do
  if [[ ! -s "$target" ]]; then
    echo "FAIL missing source: $target" >&2
    exit 3
  fi
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|no-termination-check|NO_TERMINATION_CHECK|TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|type-in-type' "$target"; then
    echo "FAIL forbidden trust escape: $target" >&2
    exit 4
  fi
  if grep -Pzo '\{!.*?!\}' "$target" >/dev/null; then
    echo "FAIL unsolved Agda hole: $target" >&2
    exit 4
  fi
done

if [[ ! -x scripts/run_agda29_parallel_check.sh ]]; then
  echo "FAIL pinned local Agda checker runner missing or not executable" >&2
  exit 5
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "FAIL python3 unavailable for independent exact E8 shell regression" >&2
  exit 6
fi
python3 scripts/check_analytic_j_tetration_e8_theta_shells.py

echo "Running pinned Agda 2.9 --safe checker on ${#targets[@]} explicit source owners"
DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh --safe "${targets[@]}"
echo "PASS exact-head focused Agda check (only if checker exited zero)"
