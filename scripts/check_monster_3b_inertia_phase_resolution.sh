#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required for inertia phase resolution" >&2
  exit 1
}

mkdir -p build/generated/DASHI/Moonshine/Generated
python -m py_compile scripts/render_monster_3b_inertia_phase_certificate.py

gap -q scripts/monster_3b_inertia_phase_resolution.g

test -s build/monster_3b_inertia_phase_resolution.json

python scripts/render_monster_3b_inertia_phase_certificate.py \
  build/monster_3b_inertia_phase_resolution.json \
  build/generated/DASHI/Moonshine/Generated/Monster3BInertiaPhaseResolutionCertificate.agda

test -s build/generated/DASHI/Moonshine/Generated/Monster3BInertiaPhaseResolutionCertificate.agda

python - <<'PY'
import json
from pathlib import Path
p = json.loads(Path("build/monster_3b_inertia_phase_resolution.json").read_text())
assert p["phase_resolution_certified"] is True
assert p["phase_resolved_multiplicity_degrees"] == [12, 78]
assert p["chosen_zeta_central_class_position"] != p["chosen_zeta_squared_central_class_position"]
rows = p["records"]
assert len(rows) == 2
expanded = []
for r in rows:
    assert r["zeta_degree"] == r["zeta_squared_degree"]
    assert r["zeta_degree"] == 729 * r["multiplicity_degree"]
    assert r["mn3b_degree"] == r["zeta_degree"] + r["zeta_squared_degree"]
    expanded += [r["multiplicity_degree"]] * r["mn3b_multiplicity"]
assert sorted(expanded) == [12, 78]
assert sum(r["mn3b_multiplicity"] * r["zeta_degree"] for r in rows) == 65610
PY

for source in \
  scripts/monster_3b_inertia_phase_resolution.g \
  scripts/render_monster_3b_inertia_phase_certificate.py \
  DASHI/Wikimedia/IbrahimMonster3BInertiaPhaseResolutionProducerSnowballExact.agda \
  DASHI/Moonshine/Monster3BCentralCharacterInertiaExact.agda; do
  test -s "$source"
done

echo "Monster 3B inertia phase-resolution checks passed"
