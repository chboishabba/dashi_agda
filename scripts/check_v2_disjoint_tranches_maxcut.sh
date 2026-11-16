#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${OPENBLAS_NUM_THREADS:=1}"
export OPENBLAS_NUM_THREADS
python -m pytest -q tests/test_v2_source_bounded_efficiency_maxcut.py tests/test_v2_fixed_shaft_pwm_negative_control.py tests/test_v2_tranche_maxcut.py tests/test_v2_lc_recovery_tranche.py
python scripts/v2_tranche_maxcut.py
python scripts/v2_lc_recovery_tranche.py
# RUN_AGDA requested only when an installed pinned compiler can actually verify files.
