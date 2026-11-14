#!/usr/bin/env bash
# Karp-21 F1 k=1 physical table: exact pinned local Agda acceptance only.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_karp21_gamma_one_bit_physical.py
owner=DASHI/Mathematics/Complexity/Karp21NativeGammaOneBitPayloadPhysicalExact.agda
test -f "$owner" || { echo "BLOCKED: missing $owner" >&2; exit 11; }
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|NO_TERMINATION_CHECK|TERMINATING|allow-unsolved-metas' "$owner"; then
 echo 'BLOCKED: unsafe or unsolved source' >&2; exit 13
fi
command -v agda >/dev/null 2>&1 || {
 echo 'BLOCKED: Agda 2.9 unavailable, independent numeric trace != golden proof' >&2
 exit 12
}
AGDA_JOBS=1 DASHI_NO_TMUX=1 \
  bash scripts/run_agda29_parallel_check.sh "$owner"
echo 'Karp k=1 gamma physical source checked; full N21 F1/F3/F4 remain OPEN.'
