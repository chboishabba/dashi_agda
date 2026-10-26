#!/usr/bin/env bash
# Backend-free source ATLAS word-order discriminator and ambient GF729 D4.
# Exact selected source bytes and finite field; NO GAP, Agda, Monster action.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m py_compile \
  scripts/monster3b_atlas_source_word_order_d4_gate.py \
  scripts/monster3b_atlas_actual_d4_word_witness.py \
  scripts/monster3b_gf729_ambient_d4_similitude_source_boundary.py
python3 scripts/monster3b_atlas_source_word_order_d4_gate.py
python3 scripts/monster3b_atlas_actual_d4_word_witness.py
python3 scripts/monster3b_gf729_ambient_d4_similitude_source_boundary.py
