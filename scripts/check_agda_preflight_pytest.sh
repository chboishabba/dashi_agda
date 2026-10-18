#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TARGET="${AGDA_PREFLIGHT_TARGET:-DASHI/Everything.agda}"
if [[ ${1:-} == *.agda ]]; then
  TARGET="$1"
  shift
fi
REFINE="${AGDA_PREFLIGHT_REFINE:-scope}"
REPORT="${AGDA_PREFLIGHT_REPORT:-.cache/agda_preflight/report.json}"
DEFAULT_SCOPE_RUNNER="$ROOT/scripts/run_agda29_parallel_check.sh --only-scope-checking {file}"
SCOPE_RUNNER="${AGDA_PREFLIGHT_SCOPE_RUNNER:-$DEFAULT_SCOPE_RUNNER}"
DEFAULT_TYPECHECK_RUNNER="$ROOT/scripts/run_agda29_parallel_check.sh {file}"
TYPECHECK_RUNNER="${AGDA_PREFLIGHT_TYPECHECK_RUNNER:-$DEFAULT_TYPECHECK_RUNNER}"

mkdir -p "$(dirname "$REPORT")"

DASHI_NO_TMUX=1 DASHI_SYNC_ONLY=1 "$ROOT/scripts/run_agda29_parallel_check.sh"
export DASHI_NO_TMUX=1
export DASHI_SKIP_RSYNC=1

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
    if [[ -n "$SCOPE_RUNNER" ]]; then
      ARGS+=("--agda-scope-runner=$SCOPE_RUNNER")
    fi
    ;;
  typecheck)
    ARGS+=(--agda-auto-refine=typecheck)
    if [[ -n "$SCOPE_RUNNER" ]]; then
      ARGS+=("--agda-scope-runner=$SCOPE_RUNNER")
    fi
    if [[ -n "$TYPECHECK_RUNNER" ]]; then
      ARGS+=("--agda-typecheck-runner=$TYPECHECK_RUNNER")
    fi
    ;;
  *)
    echo "AGDA_PREFLIGHT_REFINE must be one of: none, scope, typecheck" >&2
    exit 2
    ;;
esac

PYTHON="${PYTHON:-python}"
if [ -x "$ROOT/.venv/bin/python" ] && [ "${PYTHON}" = "python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi

exec "$PYTHON" -m pytest \
  "${ARGS[@]}" \
  "$TARGET" \
  -vv \
  -s \
  "$@"
