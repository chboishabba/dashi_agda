#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
PYTHONDONTWRITEBYTECODE=1 python -m pytest -q \
  tests/test_v2_omega_load_intervention_weld.py \
  tests/test_v2_omega_intervention_protocol.py \
  tests/test_v2_omega_split_storage_protocol.py
PYTHONDONTWRITEBYTECODE=1 python scripts/v2_omega_split_storage_protocol.py \
  --template Artifacts/v2_omega_original_v2_split_storage_empty_template_20261117.csv --blocks 4
