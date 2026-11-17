#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m pytest -q \
  tests/test_v2_omega_smooth_storage_metrology_maxcut.py \
  tests/test_v2_tranche_maxcut.py \
  tests/test_v2_lc_recovery_tranche.py \
  tests/test_v2_source_bounded_efficiency_maxcut.py \
  tests/test_v2_fixed_shaft_pwm_negative_control.py
python scripts/v2_omega_smooth_storage_metrology_maxcut.py > /dev/null
# Agda pinned kernel deliberately NOT claimed by the Python acceptance route.
