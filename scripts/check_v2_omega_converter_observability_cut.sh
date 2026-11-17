#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m pytest -q tests/test_v2_omega_converter_observability_cut.py
python scripts/v2_omega_converter_observability_cut.py >/dev/null
