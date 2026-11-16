#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OWNER=DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda
test -s "$OWNER"
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\\{!!\\}' "$OWNER"; then
  echo 'Postulate or hole found; refuse certification' >&2
  exit 1
fi
if ! command -v agda >/dev/null 2>&1; then
  echo 'Agda executable not available: D1 remains OPEN' >&2
  exit 2
fi
scripts/run_agda29_parallel_check.sh "$OWNER"
echo "PASS: pinned Agda phase matching exact-head proof check"
