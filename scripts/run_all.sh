#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ./scripts/run_all.sh [output_dir]
#
# Optional overrides:
#   BASE_CMD=... LILA_CMD=... FEATURES=... ARROW=... ./scripts/run_all.sh

OUT=${1:-runs_compare}
FEATURES=${FEATURES:-train_loss}
ARROW=${ARROW:-train_loss}

./scripts/run_compare.sh "$OUT"

python scripts/plot_training_dynamics.py \
  --baseline "$OUT/baseline.csv" \
  --lila "$OUT/lila.csv" \
  --out "$OUT/training_dynamics.png"

python scripts/delta_cone_lila.py \
  --csv "$OUT/lila.csv" \
  --features "$FEATURES" \
  --arrow "$ARROW" \
  --out "$OUT/delta_cone_rank.csv"

echo "[ok] full pipeline complete"
