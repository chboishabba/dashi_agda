#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/twob_local_outer_lift_monster_class_probe.g
test -s build/twob_local_outer_lift_monster_class_probe.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/twob_local_outer_lift_monster_class_probe.json')
d=json.loads(p.read_text())
assert d['local_group_order']==50472333605150392320
assert d['central_involution_count']>=3
assert d['outer_quotient_class_size']==1386
assert d['outer_quotient_centralizer_order']==640
assert d['possible_fusion_count']>0
# The selected central element is sourced from the normal pure-2B V4; all
# compatible Monster labels should therefore include/resolve to 2B.  Keep the
# assertion weak enough to expose ambiguity rather than manufacture uniqueness.
assert d['a_signature']['possible_monster_classes']
assert '2B' in d['a_signature']['possible_monster_classes']

print('full lift order:',d['full_lift_order'])
print('commutes with selected central 2B:',d['lift_commutes_with_selected_central_2B'])
print('possible fusion count:',d['possible_fusion_count'])
print('a Monster labels:',d['a_signature']['possible_monster_classes'])
print('h Monster labels:',d['h_signature']['possible_monster_classes'])
print('a*h Monster labels:',d['ah_signature']['possible_monster_classes'])
print('h fusion invariant?:',d['h_monster_class_fusion_invariant'])
print('a*h fusion invariant?:',d['ah_monster_class_fusion_invariant'])

if d['full_lift_order']==2 and d['lift_commutes_with_selected_central_2B']:
    print('commuting V4 candidate lift: YES')
    if d['h_monster_class_fusion_invariant'] and d['ah_monster_class_fusion_invariant']:
        print('Monster class data sufficient for next rational/mod-4 stage: YES')
    else:
        print('Monster class data still fusion-ambiguous')
else:
    print('selected preimage is not yet a commuting involutory lift; kernel-adjusted lift search required')
PY
