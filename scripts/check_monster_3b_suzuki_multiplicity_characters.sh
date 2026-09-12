#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required for 6.Suz multiplicity-character discovery" >&2
  exit 1
}

mkdir -p build/generated/DASHI/Moonshine/Generated
python -m py_compile scripts/render_monster_3b_suzuki_multiplicity_certificate.py

gap -q scripts/monster_3b_suzuki_multiplicity_characters.g

test -s build/monster_3b_suzuki_multiplicity_characters.json

python scripts/render_monster_3b_suzuki_multiplicity_certificate.py \
  build/monster_3b_suzuki_multiplicity_characters.json \
  build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMultiplicityCharacterCertificate.agda

test -s build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMultiplicityCharacterCertificate.agda

python - <<'PY'
import json
from pathlib import Path
p = json.loads(Path("build/monster_3b_suzuki_multiplicity_characters.json").read_text())
assert p["table"] == "6.Suz"
assert p["outer_table"] == "6.Suz.2"
assert p["label_source"] == "CTblLib AtlasLabelsOfIrreducibles(short)"
assert p["source_native_729_tensor_factorisation"] is True
assert p["atlas_label_position_alignment_paid"] is True
assert p["monster_same_object_match_paid"] is False

assert len(p["faithful_degree_12_positions"]) == 2
assert len(set(p["faithful_degree_12_positions"])) == 2
assert len(p["faithful_degree_78_positions"]) == 2
assert len(set(p["faithful_degree_78_positions"])) == 2
assert len(p["faithful_degree_12_atlas_labels"]) == 2
assert len(set(p["faithful_degree_12_atlas_labels"])) == 2
assert len(p["faithful_degree_78_atlas_labels"]) == 2
assert len(set(p["faithful_degree_78_atlas_labels"])) == 2

for rows, degree, labels in (
    (p["degree_12_rows"], 12, p["faithful_degree_12_atlas_labels"]),
    (p["degree_78_rows"], 78, p["faithful_degree_78_atlas_labels"]),
):
    assert len(rows) == 2
    assert sorted(r["atlas_label"] for r in rows) == sorted(labels)
    for r in rows:
        assert r["degree"] == degree
        assert isinstance(r["position"], int) and r["position"] > 0
        assert isinstance(r["atlas_label"], str) and r["atlas_label"]
        assert {r["first_central_phase"], r["second_central_phase"]} == {"zeta", "zetaSquared"}
PY

grep -F 'faithfulDegree12AtlasLabels' \
  build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMultiplicityCharacterCertificate.agda >/dev/null
grep -F 'faithfulDegree78AtlasLabels' \
  build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMultiplicityCharacterCertificate.agda >/dev/null
grep -F 'monsterSameObjectMatchPaid = false' \
  build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMultiplicityCharacterCertificate.agda >/dev/null

echo "Monster 3B source-native 6.Suz multiplicity-character checks passed"
