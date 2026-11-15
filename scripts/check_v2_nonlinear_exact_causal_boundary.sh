#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
python -m pytest -q \
  tests/test_v2_nonlinear_exact_causal_boundary.py \
  tests/test_v2_exact_multirate_periodic_port.py \
  tests/test_v2_waveguide_motor_port_maxcut.py
if [[ "${RUN_AGDA:-0}" == 1 ]]; then
  command -v agda >/dev/null 2>&1 || { echo 'Agda kernel requested but unavailable; NOT PASS' >&2; exit 42; }
  echo 'Agda compiler present; run the canonical pinned Agda acceptance separately for all source modules.' >&2
  exit 43
fi
printf 'Kernel: NOT RUN. Model exact proof and numeric tests do not imply Agda acceptance.\n'