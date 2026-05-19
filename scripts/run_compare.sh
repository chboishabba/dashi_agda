#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ./scripts/run_compare.sh [output_dir]
#
# Override the model commands without editing the script:
#   BASE_CMD='python my_baseline.py --model baseline' \
#   LILA_CMD='python my_lila.py --model lila' \
#   ./scripts/run_compare.sh

OUT=${1:-runs_compare}
STEPS=${STEPS:-50000}
BASE_CMD=${BASE_CMD:-"python train_baseline.py"}
LILA_CMD=${LILA_CMD:-"python train_lila.py"}

run_with_log() {
  local cmd="$1"
  local log_path="$2"
  bash -lc "$cmd --steps $STEPS --log \"${log_path}\""
}

mkdir -p "$OUT"

echo "[info] running baseline model..."
run_with_log "$BASE_CMD" "$OUT/baseline.csv"

echo "[info] running LILA model..."
run_with_log "$LILA_CMD" "$OUT/lila.csv"

echo "[info] done. Logs in $OUT"
