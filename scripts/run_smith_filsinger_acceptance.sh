#!/usr/bin/env bash
# Exact-head proof acceptance. This script NEVER certifies original physical measurements.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MODE="${1:---full}"
case "$MODE" in --full|--python-only) ;; *) echo "usage: $0 [--full|--python-only]" >&2; exit 2 ;; esac
command -v git >/dev/null
command -v python3 >/dev/null
HEAD="$(git rev-parse --verify HEAD)"
# Reject changed tracked inputs but ignore generated Agda caches.
if ! git diff --quiet HEAD -- .; then
  echo "REJECT: tracked checkout differs from acceptance commit" >&2
  exit 2
fi
# Only project-owned source. The third-party pinned stdlib is intentionally untracked.
if git ls-files --others --exclude-standard -- DASHI scripts .github/workflows | grep -E "\.(agda|py|sh|nix|ya?ml)$" >/dev/null; then
  echo "REJECT: untracked source, proof or workflow inputs" >&2
  exit 2
fi
RECEIPT_DIR="${SMITH_FILSINGER_RECEIPT_DIR:-$ROOT/.filsinger-acceptance}"
mkdir -p "$RECEIPT_DIR"
rm -f "$RECEIPT_DIR/acceptance-pass.txt"
LOG="$RECEIPT_DIR/acceptance.log"
: > "$LOG"
printf "commit=%s\nmode=%s\n" "$HEAD" "$MODE" | tee -a "$LOG"
TESTS=(
  scripts/test_smith_filsinger_original_gate_evidence.py
  scripts/test_smith_filsinger_signed_vi_intervals.py
  scripts/test_smith_filsinger_restored_cycle_intervals.py
  scripts/test_smith_filsinger_restored_cycle_raw_replay.py
)
for test in "${TESTS[@]}"; do
  test -s "$test"
  echo "RUN $test" | tee -a "$LOG"
  python3 "$test" 2>&1 | tee -a "$LOG"
done
if [[ "$MODE" == --full ]]; then
  echo "RUN real pinned Agda proof checker" | tee -a "$LOG"
  bash scripts/check_smith_filsinger_formal_weld_agda29.sh 2>&1 | tee -a "$LOG"
  STATUS="ACCEPTED_PYTHON_AND_PINNED_AGDA"
else
  STATUS="PYTHON_ONLY_NO_AGDA_ACCEPTANCE"
fi
printf "commit=%s\nstatus=%s\n" "$HEAD" "$STATUS" > "$RECEIPT_DIR/acceptance-pass.txt"
cat "$RECEIPT_DIR/acceptance-pass.txt"
echo "Original Maxwell calibration, independent replenishment and weather causality remain separate open physical gates."
