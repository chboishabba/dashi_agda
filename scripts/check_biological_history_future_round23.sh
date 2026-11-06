#!/usr/bin/env bash
# Execute with: bash scripts/check_biological_history_future_round23.sh
# Missing Agda is a failed acceptance gate, never a successful kernel receipt.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT=DASHI/EverythingBiologicalHistoryFutureRound23.agda
MODULE=DASHI/Biology/Physical/BiologicalHistoryFutureQuotientExact.agda
REGRESSION=scripts/check_biological_history_future_quotient.py

test -s "$ROOT"
test -s "$MODULE"
test -s "$REGRESSION"

if grep -vE '^[[:space:]]*--' "$MODULE" \
  | grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
  echo "Unsafe proof escape in $MODULE" >&2
  exit 1
fi

for theorem in \
  projectionCommutes projectionAfterTrace traceAgreementFromCoarse \
  futureSufficientCodeIsSafe sameSignalDistinguishesFuture \
  morphologyOnlyNotFutureSafe memoryBlindProjectionNotFutureSafe \
  markerStatesAreFutureEquivalent spatialProjectionCommutes \
  localEdgeResponseSurvivesProjection; do
  grep -q "$theorem" "$MODULE" || {
    echo "Missing load-bearing theorem: $theorem" >&2
    exit 1
  }
done

python3 "$REGRESSION"

if ! command -v agda >/dev/null 2>&1; then
  echo "FAIL CLOSED: Agda unavailable; finite regression is not kernel acceptance." >&2
  exit 2
fi

agda -i . -i src "$ROOT"
echo "Agda kernel typecheck accepted root: $ROOT"
