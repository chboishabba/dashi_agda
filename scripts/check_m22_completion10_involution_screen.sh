#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build

gap -q scripts/m22_completion10_involution_screen.g

test -s build/m22_completion10_involution_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/m22_completion10_involution_screen.json")
data = json.loads(p.read_text())

assert data["group"] == "M22"
assert data["expected_order"] == 443520
assert data["expected_dimension"] == 10
assert data["completion10_target"] == {
    "rank_g_minus_i": 5,
    "fixed_dimension": 5,
}
assert data["representation_count"] >= 1
assert data["involution_row_count"] >= 1

rows = []
for rep in data["representations"]:
    assert "f2r10" in rep["repname"]
    assert rep["involution_classes"]
    for row in rep["involution_classes"]:
        assert row["rank_g_minus_i"] + row["fixed_dimension"] == 10
        assert row["square_zero"] is True
        assert row["matches_J2x5"] == (
            row["rank_g_minus_i"] == 5 and row["fixed_dimension"] == 5
        )
        if row["matches_J2x5"]:
            assert row["pair_swap_basis_rank"] == 10
            assert row["pair_swap_basis_verified"] is True
        else:
            assert row["pair_swap_basis_verified"] is False
        rows.append((rep["repname"], row))

matches = [(name, row) for name, row in rows if row["matches_J2x5"]]
assert data["matching_J2x5_row_count"] == len(matches)

print("M22 10d GF(2) representations:", data["representation_count"])
for name, row in rows:
    print(
        name,
        "class_size=", row["class_size"],
        "rank(g-I)=", row["rank_g_minus_i"],
        "fixdim=", row["fixed_dimension"],
        "J2^5=", row["matches_J2x5"],
        "five-pair-basis=", row["pair_swap_basis_verified"],
    )
print("J2^5 matches:", len(matches))
PY
