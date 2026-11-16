#!/usr/bin/env bash
# Negative control: reuses existing DASHI nonlinear coupled/averaged-PWM model.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export OPENBLAS_NUM_THREADS="${OPENBLAS_NUM_THREADS:-1}"
python -m pytest -q tests/test_v2_fixed_shaft_pwm_negative_control.py
python scripts/v2_fixed_shaft_pwm_negative_control.py > Artifacts/v2_fixed_shaft_pwm_negative_control_receipt.json
python - <<'PY'
import json
r=json.load(open('Artifacts/v2_fixed_shaft_pwm_negative_control_receipt.json'))
assert len(r['arms'])==5
assert all(v['feasible'] and v['magnetically_periodic_2pct'] for v in r['arms'].values())
print('Finite averaged-bus source-independent negative control PASS; V2 hardware/Agda NOT TESTED')
PY
