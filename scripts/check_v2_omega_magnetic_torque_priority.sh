#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PYTHONPATH="$ROOT/scripts" python -m pytest -q "$ROOT/tests/test_v2_omega_magnetic_torque_priority.py"
PYTHONPATH="$ROOT/scripts" python "$ROOT/scripts/v2_omega_magnetic_torque_priority.py" > "$ROOT/Artifacts/v2_omega_magnetic_torque_priority_20261117.json"
