#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
INCLUDE_HEAVY=0
PLAN_ONLY=0
FROM_TARGET=""
REPORT_DIR="${DASHI_REPO_CHECK_REPORT_DIR:-$REPO_ROOT/.cache/agda-repo-check}"

usage() {
  cat <<'EOF'
Usage: scripts/run_agda29_repo_check.sh [options]

Typecheck every maintained first-party Agda source independently of the
Everything import hierarchy. By default, targets whose import closure reaches
YM/NS/Balaban heavy lanes are left out operationally and reported separately.
They remain live and can be checked with --include-heavy or focused runs.

Options:
  --include-heavy       include YM/NS/Balaban and all targets depending on them
  --plan-only           generate the exact target reports but do not run Agda
  --from PATH           resume at PATH in the deterministic target ordering
  --report-dir DIR      write target/skip/summary files under DIR
  -h, --help            show this help
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --include-heavy)
      INCLUDE_HEAVY=1
      shift
      ;;
    --plan-only)
      PLAN_ONLY=1
      shift
      ;;
    --from)
      [ "$#" -ge 2 ] || { echo "--from requires a path" >&2; exit 2; }
      FROM_TARGET="$2"
      shift 2
      ;;
    --report-dir)
      [ "$#" -ge 2 ] || { echo "--report-dir requires a directory" >&2; exit 2; }
      REPORT_DIR="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

mkdir -p "$REPORT_DIR"
TARGETS_FILE="$REPORT_DIR/targets.txt"
HEAVY_FILE="$REPORT_DIR/heavy-or-tainted-skipped.txt"
SUMMARY_FILE="$REPORT_DIR/summary.json"

planner=(python3 "$REPO_ROOT/scripts/plan_agda_typecheck_targets.py"
  --root "$REPO_ROOT"
  --output "$TARGETS_FILE"
  --heavy-output "$HEAVY_FILE"
  --json "$SUMMARY_FILE")
if [ "$INCLUDE_HEAVY" = "1" ]; then
  planner+=(--include-heavy)
fi
"${planner[@]}"

mapfile -t TARGETS < "$TARGETS_FILE"

if [ -n "$FROM_TARGET" ]; then
  resumed=()
  found=0
  for target in "${TARGETS[@]}"; do
    if [ "$found" = "0" ] && [ "$target" = "$FROM_TARGET" ]; then
      found=1
    fi
    if [ "$found" = "1" ]; then
      resumed+=("$target")
    fi
  done
  if [ "$found" = "0" ]; then
    echo "resume target not present in current plan: $FROM_TARGET" >&2
    exit 2
  fi
  TARGETS=("${resumed[@]}")
fi

printf 'Repository Agda check: %d selected targets' "${#TARGETS[@]}"
if [ "$INCLUDE_HEAVY" = "1" ]; then
  printf ' (heavy included)\n'
else
  printf ' (heavy dependency closure omitted operationally)\n'
fi
printf 'Plan: %s\n' "$TARGETS_FILE"
printf 'Heavy/tainted skip report: %s\n' "$HEAVY_FILE"
printf 'Summary: %s\n' "$SUMMARY_FILE"

if [ "$PLAN_ONLY" = "1" ]; then
  exit 0
fi

if [ "${#TARGETS[@]}" -eq 0 ]; then
  echo "no targets selected" >&2
  exit 2
fi

# One wrapper invocation means one shadow-tree/cache setup. The wrapper then
# checks each target in deterministic order and stops at the first failing
# module, which is the concrete repair frontier for the next iteration.
exec "$REPO_ROOT/scripts/run_agda29_parallel_check.sh" "${TARGETS[@]}"
