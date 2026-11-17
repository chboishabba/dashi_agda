#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHONDONTWRITEBYTECODE=1 python -m unittest discover -s "$ROOT/tests" -p 'test_v2_omega_coupled_magnetic_torque.py' -v
python "$ROOT/scripts/v2_omega_coupled_magnetic_torque.py" > "$ROOT/Artifacts/v2_omega_coupled_magnetic_torque_receipt_20261117.json"
