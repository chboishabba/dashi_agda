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
assert d['two_block_count']>0
assert isinstance(d['unique_degree24_brauer_position'],int)
assert d['unique_degree24_brauer_position']>=1
assert isinstance(d['unique_degree24_brauer_block'],int)
assert d['unique_degree24_brauer_block']>=1
assert len(d['brauer_irreducible_block_numbers'])==d['brauer_character_count']
assert all(isinstance(x,int) and x>=1 for x in d['brauer_irreducible_block_numbers'])
assert d['degree_98304_positions']
assert d['degree_98280_positions']
assert d['degree_299_positions']
assert d['candidate_count']>0, d
assert d['strong_candidate_count']>0, d
assert d['rigid_support_candidate_count']>0, d
assert d['rigid_block_candidate_count']>0, d
assert d['residual_24_unique_simple_identified'] is True
assert d['jh_common_98280_plus_residual24_pattern_found'] is True
assert d['common_98280_support_separated_from_residual_lanes'] is True
assert d['common_98280_block_separated_from_residual_lanes'] is True
assert d['block_idempotent_split_available'] is True
for c in d['strong_candidates']:
    r24=c['residual_24_sparse_with_block']
    assert len(r24)==1 and r24[0][1]==24 and r24[0][2]==1
    assert r24[0][0]==d['unique_degree24_brauer_position']
    assert r24[0][3]==d['unique_degree24_brauer_block']
    assert c['residual_is_unique_degree24_simple'] is True
    assert sum(row[1]*row[2] for row in c['residual_276_sparse_with_block'])==276
for c in d['rigid_support_candidates']:
    assert c['common_98280_disjoint_from_residual24'] is True
    assert c['common_98280_disjoint_from_residual276'] is True
    assert set(c['common_98280_support']).isdisjoint(c['residual_24_support'])
    assert set(c['common_98280_support']).isdisjoint(c['residual_276_support'])
for c in d['rigid_block_candidates']:
    assert c['common_98280_block_disjoint_from_residual24'] is True
    assert c['common_98280_block_disjoint_from_residual276'] is True
    assert set(c['common_98280_block_support']).isdisjoint(c['residual_24_block_support'])
    assert set(c['common_98280_block_support']).isdisjoint(c['residual_276_block_support'])
assert d['actual_norm_map_98280_isomorphism_paid'] is False
assert d['actual_tate_exterior_square_weld_paid'] is False
print('2B centralizer 2-modular cancellation candidates:',d['candidate_count'])
print('unique degree-24 Brauer simple position:',d['unique_degree24_brauer_position'])
print('unique degree-24 Brauer simple block:',d['unique_degree24_brauer_block'])
print('strong residual-24 candidates:',d['strong_candidate_count'])
print('rigid support-separated candidates:',d['rigid_support_candidate_count'])
print('rigid 2-block-separated candidates:',d['rigid_block_candidate_count'])
print('residual quotient simple type is uniquely the 24d Brauer module: PASS')
print('common and residual constituents lie in disjoint 2-blocks: PASS')
print('block-idempotent common/residual split available: PASS')
print('actual norm matrix remains source-native data; same-object promotion is still fail-closed')
PY
