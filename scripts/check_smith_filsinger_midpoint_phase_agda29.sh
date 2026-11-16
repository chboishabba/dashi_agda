#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OWNER=DASHI/Physics/Motors/SmithFilsingerMidpointPhaseWorkExact.agda
test -s "$OWNER"
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!!\}' "$OWNER"; then
  echo 'Unjustified postulate or proof hole' >&2; exit 1
fi
# Reuse repository-pinned Agda wrapper; no counterfeit checker success.
scripts/run_agda29_parallel_check.sh "$OWNER"
echo 'PASS pinned Agda midpoint phase work owner'
