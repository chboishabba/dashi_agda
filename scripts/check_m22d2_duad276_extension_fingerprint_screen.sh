#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/m22d2_duad276_extension_fingerprint_screen.g
test -s build/m22d2_duad276_extension_fingerprint_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/m22d2_duad276_extension_fingerprint_screen.json')
d=json.loads(p.read_text())
assert d['ambient_dimension']==276
assert d['m22d2_order']==887040
assert d['composition_series_dimensions'][0]==0
assert d['composition_series_dimensions'][-1]==276
assert sum(d['composition_factor_dimensions'])==276
assert 0 <= d['radical_dimension'] <= 276
assert 0 <= d['socle_dimension'] <= 276
assert d['endomorphism_algebra_dimension'] >= 1
assert sum(d['indecomposable_dimensions'])==276
rows=d['two_singular_class_rows']
assert rows
assert any(r['order']==2 for r in rows)
for r in rows:
    assert r['rank_g_minus_i'] + r['fixed_dimension'] == 276
    assert r['nilpotency_index_g_minus_i'] >= 0
assert d['actual_2b_tate_extension_fingerprint_compared'] is False
print('radical dimension:',d['radical_dimension'])
print('socle dimension:',d['socle_dimension'])
print('endomorphism algebra dimension:',d['endomorphism_algebra_dimension'])
print('indecomposable dimensions:',d['indecomposable_dimensions'])
print('2-singular rows:',len(rows))
print('actual Tate comparison: intentionally false')
PY
