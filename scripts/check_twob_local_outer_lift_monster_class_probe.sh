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
assert d['fixed_central_involution_count']>=1
assert d['outer_quotient_class_size']==1386
assert d['outer_quotient_centralizer_order']==640
assert d['possible_fusion_count']>0
assert d['lift_commutes_with_selected_central_2B'] is True
assert d['a_signature']['order']==2
assert d['a_signature']['possible_monster_classes']
assert '2B' in d['a_signature']['possible_monster_classes']

# Exploratory/fail-closed policy: an order-4 full lift is real information and
# does not get silently rewritten as the desired involution.  Only when h and
# ah are actual involutions and all three Monster labels are fusion-invariant
# do we demand the rational V4 trace decomposition.
if d['full_lift_order']==2 and d['product_order']==2:
    if (d['a_monster_class_fusion_invariant'] and
        d['h_monster_class_fusion_invariant'] and
        d['ah_monster_class_fusion_invariant']):
        assert d['weight_two_trace_a'] is not None
        assert d['weight_two_trace_h'] is not None
        assert d['weight_two_trace_ah'] is not None
        ms=d['v4_rational_eigenspace_multiplicities']
        assert ms is not None and len(ms)==4
        assert sum(ms)==196884

print('full lift order:',d['full_lift_order'])
print('product order:',d['product_order'])
print('fixed central 2B count:',d['fixed_central_involution_count'])
print('possible fusion count:',d['possible_fusion_count'])
print('a Monster labels:',d['a_signature']['possible_monster_classes'])
print('h Monster labels:',d['h_signature']['possible_monster_classes'])
print('a*h Monster labels:',d['ah_signature']['possible_monster_classes'])
print('V4 eigenspace multiplicities:',d['v4_rational_eigenspace_multiplicities'])
print('2B local outer-lift class probe: PASS (exploratory receipt)')
PY
