#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/co1_f2_frobenius24_sym2_300_hom_uniqueness_screen.g

test -s build/co1_f2_frobenius24_sym2_300_hom_uniqueness_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/co1_f2_frobenius24_sym2_300_hom_uniqueness_screen.json')
d=json.loads(p.read_text())
assert d['co1_order']==4157776806543360000
assert d['natural_dimension']==24
assert d['symmetric_square_dimension']==300
assert d['explicit_frobenius_rank']==24
assert d['hom_24_to_sym2_dimension']>0
assert all(r==24 for r in d['hom_basis_ranks'])
# This screen is intentionally decisive: if uniqueness fails, the residual
# 24->300 lane is not rigid and the vertical weld must retain that ambiguity.
assert d['hom_24_to_sym2_dimension']==1, d
assert d['unique_nonzero_hom_line'] is True
assert d['explicit_frobenius_spans_hom'] is True
assert d['actual_norm_residual_24_map_identified'] is False
assert d['common_98280_map_identified'] is False
print('Hom_Co1(24,Sym2(24)) dimension:',d['hom_24_to_sym2_dimension'])
print('unique nonzero map is explicit Frobenius-square embedding: PASS')
print('actual norm residual map / common 98280 map remain same-object receipts')
PY
