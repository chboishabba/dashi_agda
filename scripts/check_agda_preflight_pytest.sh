#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TARGET="${AGDA_PREFLIGHT_TARGET:-DASHI/Everything.agda}"
REFINE="${AGDA_PREFLIGHT_REFINE:-scope}"
REPORT="${AGDA_PREFLIGHT_REPORT:-.cache/agda_preflight/report.json}"

mkdir -p "$(dirname "$REPORT")"

ARGS=(
  --agda-preflight
  --agda-deps
  --agda-root "$ROOT"
  --agda-compact
  --agda-report-json "$REPORT"
)

case "$REFINE" in
  none)
    ;;
  scope)
    ARGS+=(--agda-auto-refine=scope)
    ;;
  typecheck)
    ARGS+=(--agda-auto-refine=typecheck)
    ;;
  *)
    echo "AGDA_PREFLIGHT_REFINE must be one of: none, scope, typecheck" >&2
    exit 2
    ;;
esac

exec python -m pytest \
  "${ARGS[@]}" \
  "$TARGET" \
  -vv \
  "$@"
