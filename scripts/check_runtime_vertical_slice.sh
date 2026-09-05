#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

cp Fixtures/Runtime/empty_agent_state.json "$TMPDIR/state.json"
python3 scripts/runtime_vertical_slice.py \
  Fixtures/Runtime/kagenti_agent_created.json \
  "$TMPDIR/state.json" \
  "$TMPDIR/receipt.json"
python3 scripts/verify_runtime_vertical_slice.py "$TMPDIR/receipt.json"

agda -i . DASHI/EverythingRuntimeVerticalSlice.agda
