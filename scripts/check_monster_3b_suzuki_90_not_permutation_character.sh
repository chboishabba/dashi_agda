#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OUT="$(python3 "$ROOT/scripts/monster_3b_suzuki_90_not_permutation_character.py")"

python3 - "$OUT" <<'PY'
import json, sys
obj = json.loads(sys.argv[1])
assert obj["all_nontrivial_phase_assignments_noninteger"] is True
assert obj["permutation_character_compatible"] is False
assert obj["degrees"] == [12, 78]
assert len(obj["phase_cases"]) == 4
assert all(case["zeta_coefficient"] != 0 for case in obj["phase_cases"])
print("monster 3B Suzuki 12+78 non-permutation character check: ok")
PY
