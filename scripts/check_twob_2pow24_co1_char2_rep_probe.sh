#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null 2>&1 || { echo "GAP is required" >&2; exit 1; }
mkdir -p build
gap -q scripts/twob_2pow24_co1_char2_rep_probe.g
test -s build/twob_2pow24_co1_char2_rep_probe.json
python3 - <<'PY'
import json
from pathlib import Path
d=json.loads(Path('build/twob_2pow24_co1_char2_rep_probe.json').read_text())
assert d['representation_info_count']==len(d['rows'])
char2=[r for r in d['rows'] if r['characteristic']==2]
print('AtlasRep infos:',d['representation_info_count'])
print('characteristic-2 rows:',len(char2))
for r in char2:
    print(r)
# Exploratory probe: absence is a meaningful result, not a failure.
assert d['direct_weight_two_276_module_identified'] is False
PY
