#!/usr/bin/env bash
# Smith/Filsinger D1 reproducible acceptance; never replaces source measurements.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="${1:---full}"
case "$MODE" in --full|--python-only) ;; *) echo "usage: $0 [--full|--python-only]" >&2; exit 2;; esac
command -v git >/dev/null
command -v python3 >/dev/null

HEAD="$(git rev-parse --verify HEAD)"
test -n "$HEAD"
# A receipt for a dirty checkout cannot uniquely identify its source.
if [[ -n "$(git status --porcelain --untracked-files=all -- DASHI/Physics/Motors scripts/check_smith_filsinger* scripts/test_smith_filsinger* scripts/run_agda29_parallel_check.sh scripts/run_smith_filsinger_acceptance.sh)" ]]; then
  echo "REJECT: source/acceptance working tree differs from the recorded commit" >&2
  exit 2
fi

RECEIPT_DIR="${SMITH_FILSINGER_RECEIPT_DIR:-$ROOT/.filsinger-acceptance}"
mkdir -p "$RECEIPT_DIR"
if [[ -e "$RECEIPT_DIR/acceptance-pass.txt" ]]; then rm "$RECEIPT_DIR/acceptance-pass.txt"; fi
LOG="$RECEIPT_DIR/acceptance.log"
: > "$LOG"

printf 'commit=%s\nmode=%s\n' "$HEAD" "$MODE" | tee -a "$LOG"
for test in \
  scripts/test_smith_filsinger_original_gate_evidence.py \
  scripts/test_smith_filsinger_signed_vi_intervals.py \
  scripts/test_smith_filsinger_restored_cycle_intervals.py \
  scripts/test_smith_filsinger_restored_cycle_raw_replay.py
do
  test -s "$test"
  echo "RUN $test" | tee -a "$LOG"
  # pipefail preserves Python test failure, not just tee success.
  python3 "$test" 2>&1 | tee -a "$LOG"
done

if [[ "$MODE" == --full ]]; then
  echo "RUN pinned real Agda 2.9 proof-owner targets" | tee -a "$LOG"
  # This MUST be the repository's genuine compiler check, never a surrogate.
  bash scripts/check_smith_filsinger_formal_weld_agda29.sh 2>&1 | tee -a "$LOG"
  STATUS="ACCEPTED_PYTHON_AND_PINNED_AGDA"
else
  STATUS="PYTHON_ONLY_NO_AGDA_ACCEPTANCE"
fi

# Persist success only once EVERY requested gate returned exit 0.
printf 'commit=%s\nstatus=%s\n' "$HEAD" "$STATUS" > "$RECEIPT_DIR/acceptance-pass.txt"
cat "$RECEIPT_DIR/acceptance-pass.txt"
echo "No original-device Maxwell, independent natural replenishment or weather claim is certified."
