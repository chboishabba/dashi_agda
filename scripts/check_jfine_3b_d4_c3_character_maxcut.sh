#!/usr/bin/env bash
# Backend-free, source-conditional D4/JFine-Monster negative and constructive
# character tests. NOT an actual GAP/CTblLib or Agda/Monster normalizer receipt.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
python3 -m py_compile \
  scripts/jfine_3b_oriented_h4_d4_residual_nogo.py \
  scripts/jfine_3b_signed_c3_orbit_repair.py
python3 scripts/jfine_3b_oriented_h4_d4_residual_nogo.py
python3 scripts/jfine_3b_signed_c3_orbit_repair.py
python3 tests/test_jfine_3b_oriented_h4_d4_residual_nogo.py
python3 tests/test_jfine_3b_signed_c3_orbit_repair.py
