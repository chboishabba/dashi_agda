#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/m24_exterior_square24_duad276_screen.g
test -s build/m24_exterior_square24_duad276_screen.json
python3 - <<'PY'
import json
from pathlib import Path
d=json.loads(Path('build/m24_exterior_square24_duad276_screen.json').read_text())
assert d['pair_count']==276
assert d['exterior_action_order']==244823040
assert d['atlas_p276_action_order']==244823040
assert d['point_stabilizer_order']==887040
assert d['point_stabilizers_conjugate'] is True
assert d['permutation_representations_equivalent'] is True
assert sum(d['composition_factor_dimensions'])==276
assert d['composition_series_dimensions'][0]==0
assert d['composition_series_dimensions'][-1]==276
assert d['endomorphism_algebra_dimension']>=1
assert d['actual_2b_tate_identified'] is False
print('M24 wedge2(24) = duad p276 permutation representation: PASS')
print('composition factors:',d['composition_factor_dimensions'])
print('series:',d['composition_series_dimensions'])
print('rad/soc/end:',d['radical_dimension'],d['socle_dimension'],d['endomorphism_algebra_dimension'])
print('Tate same-object: intentionally false')
PY
