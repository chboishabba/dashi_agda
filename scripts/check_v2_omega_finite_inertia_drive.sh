#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH="${PWD}/scripts${PYTHONPATH:+:${PYTHONPATH}}"
python -m unittest discover -s tests -p 'test_v2_omega_*.py' -v
python scripts/v2_omega_finite_inertia_drive.py > Artifacts/v2_omega_finite_inertia_drive_receipt_20261117.json
