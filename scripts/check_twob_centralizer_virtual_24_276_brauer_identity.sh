#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/twob_centralizer_virtual_24_276_brauer_identity.g
test -s build/twob_centralizer_virtual_24_276_brauer_identity.json
python3 - <<'PY'
import json
from pathlib import Path
d=json.loads(Path('build/twob_centralizer_virtual_24_276_brauer_identity.json').read_text())
assert d['centralizer_order']==139511839126336328171520000
assert d['co1_order']==4157776806543360000
assert d['odd_centralizer_class_count']>0
assert d['degree_98280_character_positions']
assert d['degree_98304_character_positions']
assert d['passing_pair_count']==len(d['passing_character_pairs'])
assert d['virtual_24_identity_has_solution'] is True
assert d['virtual_276_identity_has_same_solution'] is True
assert d['passing_pair_count']>0
assert d['integral_norm_exact_sequence_paid'] is False
print('odd centralizer classes:',d['odd_centralizer_class_count'])
print('98280 candidates:',d['degree_98280_character_positions'])
print('98304 candidates:',d['degree_98304_character_positions'])
print('passing pairs:',d['passing_character_pairs'])
print('integral norm exact sequence: intentionally false')
PY
