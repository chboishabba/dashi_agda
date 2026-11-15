#!/usr/bin/env bash
# Fifth-cut target. Separate processes avoid slow cross-suite numerical state.
set -euo pipefail
cd "$(dirname "$0")/.."
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m pytest -q tests/test_v2_retarded_memory_periodic_maxcut.py
if [[ "${RUN_MEMORY_PRODUCER:-0}" == "1" ]]; then
  python scripts/v2_retarded_memory_periodic_maxcut.py > /tmp/v2_retarded_memory_maxcut_producer.json
  printf 'Retarded memory model producer: PASS (output /tmp/v2_retarded_memory_maxcut_producer.json)\n'
else
  printf 'Full numerical receipt refresh: NOT RUN (RUN_MEMORY_PRODUCER=1)\n'
fi
printf 'P0 Agda real calculus and original V2 physical welding: NOT RUN / OPEN\n'
