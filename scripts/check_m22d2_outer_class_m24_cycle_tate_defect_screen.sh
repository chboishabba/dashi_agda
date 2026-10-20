#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/m22d2_outer_class_m24_cycle_tate_defect_screen.g
test -s build/m22d2_outer_class_m24_cycle_tate_defect_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/m22d2_outer_class_m24_cycle_tate_defect_screen.json')
d=json.loads(p.read_text())
assert d['m22d2_order']==887040
assert d['ambient_dimension']==276
rows=d['outer_involution_rows']
assert rows
for r in rows:
    assert r['rank_g_minus_i'] + r['fixed_dimension'] == 276
    assert r['iterated_tate_defect_dimension'] == 276 - 2*r['rank_g_minus_i']
    assert sum(r['m24_p24_cycle_lengths']) == 24
assert d['target_class_1386_640_found'] is True
assert d['actual_2b_iterated_tate_defect_compared'] is False
print('outer involution rows:')
for r in rows:
    print(r)
print('actual 2B iterated-Tate comparison: intentionally false')
PY
