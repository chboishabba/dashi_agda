#!/usr/bin/env bash
# KSW F8 original AdS5 TT model: LOCAL evidence only; never CI promotion.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="--smoke"
if [ "$#" -gt 0 ]; then mode="$1"; fi
python3 scripts/test_ksw668_f8_moving_maxcut.py
python3 scripts/test_ksw668_f8_non_glancing_source.py
python3 scripts/ksw668_f8_non_glancing_source.py
if [ "$mode" = "--smoke" ]; then
  echo "F8 smoke accepted; three-grid and physical receiver NOT accepted."
  exit 0
fi
if [ "$mode" != "--full" ]; then
  echo "Usage: $0 --smoke | --full" >&2
  exit 2
fi
python3 scripts/ksw668_f8_refinement.py
if python3 - <<'PY'
import json
p='scripts/ksw668_f8_refinement_receipt.json'
with open(p,encoding='utf8') as f: d=json.load(f)
assert d["full_B4_converged"], "3D compact TT / electric Weyl mesh-convergence gate OPEN"
PY
then
  echo "F8 numerical provisional gate pass; Agda and physical gates remain separate."
else
  echo "F8 original compact TT receiver is NOT converged: exit 42." >&2
  exit 42
fi
