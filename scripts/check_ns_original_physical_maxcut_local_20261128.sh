#!/usr/bin/env bash
# Local exact physical-source acceptance, no GitHub CI, no kernel claims.
# Run in separate <=90s stages; checkpoint by source stage ID.
#   bash scripts/check_ns_original_physical_maxcut_local_20261128.sh r726
#   bash scripts/check_ns_original_physical_maxcut_local_20261128.sh r645
#   bash scripts/check_ns_original_physical_maxcut_local_20261128.sh all
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ "${PYTHONOPTIMIZE:-0}" != "0" ]]; then
  echo "REFUSE: PYTHONOPTIMIZE strips exact regression assertions" >&2
  exit 2
fi

run_stage() {
  local id="$1"
  local path expected actual
  case "$id" in
    r726)
      path="scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py"
      expected="682ad3452a90322111bb8179bbbc68c7a4966aa4"
      ;;
    r645)
      path="scripts/check_ns_r645_c2_original_physical_counterexample_20261128.py"
      expected="4a35e38940c756adf5e0b36212605bdc97db694b"
      ;;
    *)
      echo "Unknown stage: $id" >&2
      exit 2
      ;;
  esac
  actual="$(git hash-object "$path")"
  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL-CLOSED stale exact-source blob for $id: $actual vs $expected" >&2
    exit 3
  fi
  echo "SOURCE-MATCH $id $actual"
  # Avoid optimizations; each independent stage has its own hard 90s bound.
  timeout 90s python -B "$path"
  echo "EXACT-PHYSICAL-SOURCE-PASS $id; NOT NATIVE KERNEL ACCEPTANCE"
}

case "${1:-all}" in
  r726) run_stage r726 ;;
  r645) run_stage r645 ;;
  all) run_stage r726; run_stage r645 ;;
  *)
    echo "Usage: $0 [r726|r645|all]" >&2
    exit 2
    ;;
esac
echo "Status: original physical-real finite algebra tested; all-data NS, native Agda/Lean and continuum still OPEN."
