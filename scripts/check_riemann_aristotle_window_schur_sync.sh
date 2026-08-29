#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda
  DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || { echo "missing or empty source: $source" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  grep -F "$2" "$1" >/dev/null || {
    echo "missing required marker '$2' in $1" >&2
    exit 1
  }
}

require_pattern DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda 'residualStrictlyBelowSignalMargin'
require_pattern DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda 'splitResidualStrictlyBelowSignalMargin'
require_pattern DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda 'residualMustBeNonPositiveIsFalse'
require_pattern DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda 'entrywiseTriangleBoundRequiredByInterfaceIsFalse'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'literalWeilParityBalanceStatus'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'absoluteMassNoGoStatus'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'multiTaperSchurStatus'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'windowSeparationStatus'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'normalizedEndpointDominationStatus'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda 'canonicalRound202PatternReturn'
require_pattern DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda 'riemannHypothesisStillNotDerived'

DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda \
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda \
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
