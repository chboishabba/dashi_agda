#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/co1_normal2pow24_augmentation_hom_screen.g
test -s build/co1_normal2pow24_augmentation_hom_screen.json
python3 - <<'PY'
import json
from pathlib import Path

d=json.loads(Path('build/co1_normal2pow24_augmentation_hom_screen.json').read_text())
assert d['co1_order']==4157776806543360000
assert d['natural_dimension']==24
assert d['large_simple_dimension']==274
assert d['tensor_dimension']==6576
assert d['hom_24_to_1_dimension']==0
assert d['hom_24_to_274_dimension']==0
assert d['hom_24_tensor_274_to_1_dimension']==0
assert d['hom_24_tensor_274_to_274_dimension']==0
assert d['all_augmentation_adjacent_homs_vanish'] is True
assert d['normal_2pow24_triviality_on_any_1_274_1_filtered_module_forced'] is True
assert d['actual_tate_has_1_274_1_profile_proved'] is False
assert d['actual_tate_normal_2pow24_triviality_proved'] is False
print('Co1 augmentation Hom obstruction: PASS')
print('Hom dimensions:',{
 '24->1':d['hom_24_to_1_dimension'],
 '24->274':d['hom_24_to_274_dimension'],
 '24x274->1':d['hom_24_tensor_274_to_1_dimension'],
 '24x274->274':d['hom_24_tensor_274_to_274_dimension'],
})
PY
