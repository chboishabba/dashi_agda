#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MODE="${1:-tests}"
if [[ "$MODE" != "tests" && "$MODE" != "--agda" ]]; then
  echo "Usage: $0 [tests|--agda]" >&2
  exit 2
fi
target="DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda"
phase_owner="DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda"
python_tests=(
  scripts/test_smith_filsinger_midpoint_phase_work.py
  scripts/test_smith_filsinger_midpoint_dc_source_matching.py
  scripts/test_smith_filsinger_dynamic_replenishment.py
  scripts/test_smith_filsinger_phase_maxcut_exact.py
)
test -s "$target"
test -s "$phase_owner"
for f in "${python_tests[@]}";do test -s "$f";done
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\\{!!\\}' "$target" "$phase_owner";then
  echo "Unjustified postulate or Agda hole" >&2
  exit 1
fi
PYTHONDONTWRITEBYTECODE=1 python -m pytest -q "${python_tests[@]}"
if [[ "$MODE" == "--agda" ]];then
  scripts/run_agda29_parallel_check.sh "$target" "$phase_owner"
  echo "PASS pinned Agda dynamic-cycle source-cap owner"
else
  echo "Python tests passed; Agda kernel NOT checked. Use --agda on pinned host."
fi
