#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

mkdir -p build
python3 scripts/monster_3b_modern_restriction_degree_uniqueness.py \
  > build/monster_3b_modern_restriction_degree_uniqueness.json

test -s build/monster_3b_modern_restriction_degree_uniqueness.json

python3 - <<'PY'
import json
from pathlib import Path
p = json.loads(Path("build/monster_3b_modern_restriction_degree_uniqueness.json").read_text())
assert p["modern_protocol_candidate_count"] == 95
assert p["restriction_constituent_count"] == 4
assert p["restriction_coefficients_all_one"] is True
assert p["unique_four_constituent_degree_multiset"] is True
assert p["solution_degrees"] == [143, 17496, 65520, 113724]
assert p["total_degree"] == 196883
assert p["paired_phase_degrees"] == [17496, 113724]
assert p["multiplicity_degrees"] == [12, 78]
assert p["paired_phase_total"] == 131220
assert p["single_phase_total"] == 65610
assert p["centre_trivial_total"] == 65663
assert p["an_wilson_doi"] == "10.1112/S1461157009000059"
assert p["modern_verification_doi"] == "10.1016/j.jalgebra.2025.09.034"
assert p["oeis_authority"] is False
PY

echo "Monster 3B modern restriction degree uniqueness checks passed"
