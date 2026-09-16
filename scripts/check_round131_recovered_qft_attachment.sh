#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
  DASHI/Physics/Foundations/BalabanRound131RecoveredQFTAttachmentExact.agda
  DASHI/Physics/Foundations/BalabanRound131RecoveredQFTAttachmentValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round131 recovered-QFT attachment contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record Round131RecoveredQFTAttachment' "${files[1]}"
grep -q 'literalConstructionIsRecoveredQFT' "${files[1]}"
grep -q '^recoveredAttachmentImpliesSelectedQFTTarget :' "${files[1]}"
grep -q 'qftRecoveryAfterCoarseGrainingCommutes' "${files[1]}"
grep -q '^round131RecoveredQFTAttachmentCompilerLevel :' "${files[1]}"
grep -q '^recoveredQFTConstructionAttachmentStillRequired : Bool' "${files[1]}"

grep -q 'Attachment.round131RecoveredQFTAttachmentCompilerLevel' "${files[2]}"
grep -q 'Attachment.recoveredQFTConstructionAttachmentStillRequired' "${files[2]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round131-recovered-qft}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/round131-recovered-qft-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/BalabanRound131RecoveredQFTAttachmentValidation.agda
