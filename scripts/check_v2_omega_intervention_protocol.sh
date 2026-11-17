#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m pytest -q \
 tests/test_v2_source_bounded_efficiency_maxcut.py \
 tests/test_v2_tranche_maxcut.py \
 tests/test_v2_lc_recovery_tranche.py \
 tests/test_v2_omega_smooth_storage_metrology_maxcut.py \
 tests/test_v2_omega_converter_observability_cut.py \
 tests/test_v2_omega_robust_pulse_recovery.py \
 tests/test_v2_omega_semiconductor_loss_and_identification.py \
 tests/test_v2_omega_load_intervention_weld.py \
 tests/test_v2_omega_intervention_protocol.py
