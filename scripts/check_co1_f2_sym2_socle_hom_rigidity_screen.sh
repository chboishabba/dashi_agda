#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/co1_f2_sym2_socle_hom_rigidity_screen.g

test -s build/co1_f2_sym2_socle_hom_rigidity_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/co1_f2_sym2_socle_hom_rigidity_screen.json')
d=json.loads(p.read_text())
assert d['co1_order']==4157776806543360000
assert d['sym2_dimension']==300
assert d['composition_factor_dimensions']==[1,1,24,274]
assert d['hom_1_to_sym2_dimension']==0
assert d['hom_24_to_sym2_dimension']==1
assert d['hom_274_to_sym2_dimension']==0
assert d['unique_24_hom_rank']==24
assert d['frobenius_spans_unique_24_hom'] is True
assert d['socle_forced_single_24'] is True
assert d['socle_forced_frobenius'] is True
assert d['actual_tate_residual_image_identified'] is False
print('Co1 Sym2 socle-Hom rigidity: PASS')
PY
