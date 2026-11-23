#!/usr/bin/env bash
# F8 LXXXVII local-only original production replay.
# Run from repo root after obtaining a literal checkout; do not use CI.
# Cooperative restarts preserve original NativeCheckpoint input identity.
set -euo pipefail
cd "$(dirname "$0")/.."
work="${1:-.local-f8-lxxxvii}"
budget="${F8_SLICE_BUDGET:-12}"
max_rounds="${F8_MAX_ROUNDS:-64}"
# Pin the original production owner to the exact identical master/#1527 blobs
# audited on 2026-11-23. Git blob SHA-1 is a source identity, not a security claim.
check_blob() {
    local file="$1" expected="$2" actual
    [[ -f "$file" ]] || { echo "MISSING original producer: $file" >&2; exit 2; }
    actual="$(git hash-object "$file")"
    [[ "$actual" == "$expected" ]] || {
        echo "Original producer changed: $file expected=$expected actual=$actual" >&2
        exit 2
    }
}
check_blob scripts/ksw668_f8_tt_multipole.py 28f114fa2fd364a8569f04a7e2ace15e45ffe980
check_blob scripts/ksw668_f8_fv_source_flux.py dec4e79e3a4899952a5deceb786324bc0745982c
check_blob scripts/ksw668_f8_weak_source.py 69f35c6569667034214035d810dee06251a6d2ad
check_blob scripts/ksw668_f8_ssprk_checkpoint.py 2ef1bfbd4df98c29168a8f8b626efbecb71cdf99
check_blob scripts/run_f8_lxix_native_source_matrix.py 94e6303eab04823ab7f39244d21a32c98a300a07
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
