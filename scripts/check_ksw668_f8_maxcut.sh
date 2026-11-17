#!/usr/bin/env bash
# KSW original a=t AdS5: discover all current source-equivalent F8 regression tests.
# Full 3D numerical acceptance is separate; failures remain explicit.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="--smoke"
if [ "$#" -gt 0 ]; then mode="$1"; fi
export PYTHONPATH="scripts:."
python3 -m unittest discover -s scripts -p 'test_ksw668_f8_*.py' -v
if [ "$mode" = "--smoke" ]; then
  echo "F8 smoke PASS: all dynamically discovered local F8 tests (expected 410 after XI; verify actual unittest output)."
  echo "3D tensor/Weyl convergence, Agda, matter action and observation NOT ACCEPTED."
  exit 0
fi
if [ "$mode" = "--threegrid-XI-audit" ]; then
  python3 scripts/ksw668_f8_c3_weighted_operator_no_go.py
  python3 scripts/ksw668_f8_weak_sat_left_null_obstruction.py
  python3 scripts/ksw668_f8_threegrid_signed_failclosed.py
  echo "KSW XI exact finite operator, SBP parity and 3-grid FAIL evidence audited."
  echo "No original H/E4/E5 convergence, high-order Weyl or physical acceptance."
  exit 0
fi
if [ "$mode" = "--threegrid-XI-fine" ]; then
  python3 scripts/ksw668_f8_threegrid_signed_failclosed.py --run-grid fine
  python3 scripts/ksw668_f8_threegrid_signed_failclosed.py --accept
  exit $?
fi
if [ "$mode" = "--ternary-codec" ]; then
  python3 scripts/ksw668_f8_ternary_three_harmonic_consumer.py
  echo "F8 X Base369 unsigned ternary q0/1/2 exact channel codec and C3 physical no-go PASS."
  echo "Original source-to-both-Weyl and complete experiment still OPEN."
  exit 0
fi
if [ "$mode" = "--ternary-two-grid" ]; then
  python3 scripts/ksw668_f8_ternary_channel_drift.py --reproduce
  exit $?
fi
if [ "$mode" = "--constraint-audit" ]; then
  python3 scripts/ksw668_f8_characteristic_constraint_maxcut.py
  python3 scripts/ksw668_f8_weak_sat_constraint_no_go.py
  python3 scripts/ksw668_f8_radial_sobolev_hierarchy.py
  echo "F8 IX finite-grid constraint/radial Sobolev mathematical audit PASS."
  echo "Weak SAT boundary constraint, coupled RK3 and both-Weyl convergence OPEN."
  exit 0
fi
if [ "$mode" = "--weighted-two-grid" ]; then
  python3 scripts/ksw668_f8_weighted_SBP4_two_grid.py
  exit $?
fi
if [ "$mode" = "--normal-compare" ]; then
  python3 scripts/ksw668_f8_normal_operator_comparison.py --reproduce
  exit $?
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
echo "Usage: $0 --smoke | --threegrid-XI-audit | --threegrid-XI-fine | --ternary-codec | --ternary-two-grid | --constraint-audit | --weighted-two-grid | --normal-compare | --legacy-full | --multipole-full | --full" >&2
exit 2
