#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
PYTHONPATH=. OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python -m pytest -q tests/test_v2_waveguide_motor_port_maxcut.py
python scripts/v2_waveguide_motor_port_maxcut.py >/dev/null
printf 'DISCRETE MODEL: local tests and standalone receipt producer PASS\n'
printf 'NOT ACCEPTED: original V2 hardware, full Maxwell PDE, arbitrary hysteresis, Agda kernel\n'
