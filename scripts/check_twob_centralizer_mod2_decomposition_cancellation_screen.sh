#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/twob_centralizer_mod2_decomposition_cancellation_screen.g

test -s build/twob_centralizer_mod2_decomposition_cancellation_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/twob_centralizer_mod2_decomposition_cancellation_screen.json')
d=json.loads(p.read_text())
assert d['ordinary_character_count']>0
assert d['brauer_character_count']>0
assert d['degree_98304_positions']
assert d['degree_98280_positions']
assert d['degree_299_positions']
assert d['candidate_count']>0, d
assert d['strong_candidate_count']>0, d
assert d['rigid_support_candidate_count']>0, d
assert d['jh_common_98280_plus_residual24_pattern_found'] is True
assert d['common_98280_support_separated_from_residual_lanes'] is True
for c in d['strong_candidates']:
    r24=c['residual_24_sparse']
    assert len(r24)==1 and r24[0][1]==24 and r24[0][2]==1
    assert sum(deg*mult for _,deg,mult in c['residual_276_sparse'])==276
for c in d['rigid_support_candidates']:
    assert c['common_98280_disjoint_from_residual24'] is True
    assert c['common_98280_disjoint_from_residual276'] is True
    assert set(c['common_98280_support']).isdisjoint(c['residual_24_support'])
    assert set(c['common_98280_support']).isdisjoint(c['residual_276_support'])
assert d['actual_norm_map_98280_isomorphism_paid'] is False
assert d['actual_tate_exterior_square_weld_paid'] is False
print('2B centralizer 2-modular cancellation candidates:',d['candidate_count'])
print('strong residual-24 candidates:',d['strong_candidate_count'])
print('rigid support-separated candidates:',d['rigid_support_candidate_count'])
print('Jordan-Hoelder 98304 = 98280 + 24 pattern: PASS')
print('common 98280 support cannot leak into residual 24/276 lanes: PASS')
print('actual norm-map placement remains intentionally false')
PY
