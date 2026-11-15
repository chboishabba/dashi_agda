#!/usr/bin/env bash
# KSW original a=t AdS5: 184 DISTINCT source-equivalent F8 regression cases.
# Full 3D numerical acceptance is separate; failures remain explicit.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="--smoke"
if [ "$#" -gt 0 ]; then mode="$1"; fi
export PYTHONPATH="scripts:."
python3 -m unittest discover -s scripts -p 'test_ksw668_f8_*.py' -v
if [ "$mode" = "--smoke" ]; then
  echo "F8 smoke PASS only: 184 distinct local source-level tests."
  echo "3D tensor/Weyl convergence, Agda, matter action and observation NOT ACCEPTED."
  exit 0
fi
if [ "$mode" = "--multipole-full" ]; then
  python3 scripts/ksw668_f8_tt_multipole_refinement.py
  exit $?
fi
if [ "$mode" = "--legacy-full" ]; then
  python3 scripts/ksw668_f8_refinement.py
  python3 - <<'PY'
import json
with open('scripts/ksw668_f8_refinement_receipt.json',encoding='utf8') as f:
    result=json.load(f)
assert result['full_B4_converged'], 'legacy 3D Fourier/Weyl convergence OPEN'
PY
  exit $?
fi
if [ "$mode" = "--full" ]; then
  status=0
  if ! python3 scripts/ksw668_f8_refinement.py; then status=42; fi
  if ! python3 - <<'PY'
import json
with open('scripts/ksw668_f8_refinement_receipt.json',encoding='utf8') as f:
    result=json.load(f)
assert result['full_B4_converged'], 'legacy Fourier receiver FAILED'
PY
  then status=42; fi
  if ! python3 scripts/ksw668_f8_tt_multipole_refinement.py; then status=42; fi
  if [ "$status" -ne 0 ]; then
    echo "F8 B4 convergence remains OPEN; physical and formal gates not promoted." >&2
    exit 42
  fi
  echo "Provisional numeric thresholds met; analytic/Agda/physical gates separate."
  exit 0
fi
echo "Usage: $0 --smoke | --legacy-full | --multipole-full | --full" >&2
exit 2
