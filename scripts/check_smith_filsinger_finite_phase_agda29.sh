#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OWNER=DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda
test -s "$OWNER"
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!!\}' "$OWNER"; then
  echo 'Postulate or hole found; refuse certification' >&2
  exit 1
fi
# The pinned wrapper can locate Agda through Nix even when 'agda' is not on PATH.
test -x scripts/run_agda29_parallel_check.sh
scripts/run_agda29_parallel_check.sh "$OWNER"
echo "PASS: pinned Agda phase matching exact-head proof check"
