#!/usr/bin/env bash
# F8 LXXXVII local-only original production replay.
# Run from repo root after obtaining a literal checkout; do not use CI.
# Cooperative restarts preserve original NativeCheckpoint input identity.
set -euo pipefail
cd "$(dirname "$0")/.."
work="${1:-.local-f8-lxxxvii}"
budget="${F8_SLICE_BUDGET:-12}"
max_rounds="${F8_MAX_ROUNDS:-64}"
mkdir -p "$work"
for label in A0 A1 C0 C1; do
    finished=0
    for ((round=1; round<=max_rounds; round++)); do
        echo "[$label] local 90s guard round=$round budget=$budget" >&2
        set +e
        OPENBLAS_NUM_THREADS=1 NUMBA_NUM_THREADS=2 timeout --signal=TERM --kill-after=3s 90s \
            python -u scripts/run_f8_lxix_native_source_matrix.py "$label" \
              --work "$work" --budget "$budget" \
              > "$work/$label.round$round.log" 2>&1
        status=$?
        set -e
        if [[ $status -eq 0 ]]; then
            test -s "$work/$label.json" || { echo "missing $label JSON" >&2; exit 1; }
            echo "[$label] native production exit=0 JSON ready" >&2
            finished=1
            break
        fi
        if [[ $status -eq 75 ]]; then
            echo "[$label] cooperative checkpoint exit=75; resume next bounded round" >&2
        else
            echo "[$label] fatal status=$status; do NOT claim acceptance" >&2
            tail -n 35 "$work/$label.round$round.log" >&2 || true
            exit "$status"
        fi
    done
    [[ $finished -eq 1 ]] || { echo "[$label] exhausted $max_rounds rounds" >&2; exit 1; }
done
python -u scripts/check_f8_lxxxvii_native_96_receipt.py --work "$work" \
  > "$work/production-96-parity.json"
echo "PASS: four original end-to-end native runs and 96 signed receipt comparisons" >&2
cat "$work/production-96-parity.json"
