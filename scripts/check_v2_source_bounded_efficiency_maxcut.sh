#!/usr/bin/env bash
# Source-independent four-way steelman acceptance. Nothing here verifies V2 hardware.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export OPENBLAS_NUM_THREADS="${OPENBLAS_NUM_THREADS:-1}"
python -m pytest -q tests/test_v2_source_bounded_efficiency_maxcut.py
python scripts/v2_source_bounded_efficiency_maxcut.py > Artifacts/v2_source_bounded_efficiency_receipt.json
python - <<'PY'
import json
p='Artifacts/v2_source_bounded_efficiency_receipt.json'
r=json.load(open(p))
assert len(r['main']['results']) == 4
assert all(abs(v['accounting_residual_w']) < 1e-8 for v in r['main']['results'].values())
assert all(v['same_shaft_w'] for v in r['main']['results'].values())
assert r['intervention']['required_loss_delta_w'] == -45.
print('Receipt checked:', p, 'original apparatus and Agda-kernel proof: NOT RUN')
PY
