#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
python3 scripts/check_ym_round83_to_527_merged_maxcut.py --json

if [[ -z "${AGDA_BIN:-}" ]] && command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
fi
DASHI_NO_TMUX=1 AGDA_JOBS=1 \
  bash scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/YangMillsClayMergedResearchAndResidualCountRound528Exact.agda
echo "Round528 count root checked; 43-leaf manifest source match checked."
echo "NO source-specific physical theorem is thereby proved."
