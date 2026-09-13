#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TARGET="DASHI/Physics/Closure/NSForensicSignedRouteLineageAuditExact.agda"

printf 'Checking earliest-forward NS forensic signed-route ledger: %s\n' "$TARGET"
exec nix develop .# --command bash scripts/run_agda29_parallel_check.sh "$TARGET"
