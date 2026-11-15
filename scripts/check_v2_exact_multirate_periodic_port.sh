#!/usr/bin/env bash
# Exact rational multirate line/winding/memory subgate; independent of heavy legacy PWM.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
python scripts/v2_exact_multirate_periodic_port.py > /tmp/v2_exact_multirate_periodic_port_verification.json
python -m pytest -q tests/test_v2_exact_multirate_periodic_port.py
printf 'NO Agda kernel, smooth V2 hardware, or full PDE claim\n'
