#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/co1_f2_sym2_unique_minimal24_submodule_screen.g

test -s build/co1_f2_sym2_unique_minimal24_submodule_screen.json
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build/co1_f2_sym2_unique_minimal24_submodule_screen.json')
d=json.loads(p.read_text())
assert d['co1_order']==4157776806543360000
assert d['symmetric_square_dimension']==300
assert d['minimal_24_submodule_count']==1
assert d['unique_minimal_24_submodule'] is True
assert d['unique_minimal_24_equals_frobenius'] is True
assert d['socle_dimension']==24
assert d['socle_equals_frobenius'] is True
assert d['actual_tate_residual_image_identified'] is False
print('Co1 Sym2 unique minimal 24-submodule: PASS')
print('minimal dimensions:',d['minimal_submodule_dimensions'])
print('socle dimension:',d['socle_dimension'])
PY
