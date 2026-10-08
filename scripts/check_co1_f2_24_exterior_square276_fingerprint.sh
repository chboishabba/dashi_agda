#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/co1_f2_24_exterior_square276_fingerprint.g
test -s build/co1_f2_24_exterior_square276_fingerprint.json
python3 - <<'PY'
import json
from pathlib import Path
d=json.loads(Path('build/co1_f2_24_exterior_square276_fingerprint.json').read_text())
assert d['co1_order']==4157776806543360000
assert d['source_module_dimension']==24
assert d['exterior_square_dimension']==276
assert sum(d['composition_factor_dimensions'])==276
assert len(d['composition_factor_kinds'])==len(d['composition_factor_dimensions'])
assert d['composition_series_dimensions'][0]==0
assert d['composition_series_dimensions'][-1]==276
assert sum(d['indecomposable_dimensions'])==276
assert d['endomorphism_algebra_dimension']>=1
assert d['trivial_factor_count']+d['atlas_274_factor_count']+d['unidentified_factor_count']==len(d['composition_factor_dimensions'])
assert d['normal_2pow24_triviality_on_tate_proved'] is False
assert d['actual_2b_tate_identified_with_exterior_square'] is False
print('Co1 wedge2(24) factors:',d['composition_factor_dimensions'])
print('factor kinds:',d['composition_factor_kinds'])
print('1/274/1 profile?:',d['one_274_one_composition_profile'])
print('series:',d['composition_series_dimensions'])
print('rad/soc/end:',d['radical_dimension'],d['socle_dimension'],d['endomorphism_algebra_dimension'])
print('indecomposable:',d['indecomposable_dimensions'],'module indecomposable?',d['module_indecomposable'])
PY
