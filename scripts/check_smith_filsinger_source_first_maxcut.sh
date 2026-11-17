#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# Source-first evaluation precedes an unconstrained full 3D Maxwell solve.
# These tests use conditional mathematical models, NOT original physical data.
python -m pytest -q \
  scripts/test_smith_filsinger_midpoint_phase_work.py \
  scripts/test_smith_filsinger_midpoint_dc_source_matching.py \
  scripts/test_smith_filsinger_dynamic_replenishment.py \
  scripts/test_smith_filsinger_source_first.py \
  scripts/test_smith_filsinger_local_maxwell_port.py
python scripts/check_smith_filsinger_source_first.py
python scripts/check_smith_filsinger_local_maxwell_port.py
echo "PASS conditional F10/F13-F16 source-first models; no original physical or Agda kernel receipt"
