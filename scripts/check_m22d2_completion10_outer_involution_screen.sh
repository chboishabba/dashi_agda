#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build

gap -q scripts/m22d2_completion10_outer_involution_screen.g

test -s build/m22d2_completion10_outer_involution_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/m22d2_completion10_outer_involution_screen.json")
data = json.loads(p.read_text())

assert data["group"] == "M22.2"
assert data["expected_order"] == 887040
assert data["expected_derived_order"] == 443520
assert data["expected_dimension"] == 10
assert data["target"] == {"rank_g_minus_i": 5, "fixed_dimension": 5}
assert data["representation_count"] >= 1
assert data["outer_involution_row_count"] >= 1

all_matches = 0
outer_matches = 0
outer_rows = 0
for rep in data["representations"]:
    assert rep["m22_restriction_matches"]
    assert all("f2r10" in x for x in rep["m22_restriction_matches"])
    assert rep["involution_classes"]
    for row in rep["involution_classes"]:
        assert row["rank_g_minus_i"] + row["fixed_dimension"] == 10
        assert row["square_zero"] is True
        expected = row["rank_g_minus_i"] == 5 and row["fixed_dimension"] == 5
        assert row["matches_J2x5"] == expected
        if row["outer"]:
            outer_rows += 1
        if expected:
            all_matches += 1
            assert row["pair_swap_basis_rank"] == 10
            assert row["pair_swap_basis_verified"] is True
            if row["outer"]:
                outer_matches += 1
        else:
            assert row["pair_swap_basis_verified"] is False

assert data["outer_involution_row_count"] == outer_rows
assert data["all_J2x5_match_count"] == all_matches
assert data["outer_J2x5_match_count"] == outer_matches
assert data["actual_2b_tate_subquotient_identified"] is False

print("M22:2 10d representations:", data["representation_count"])
print("Outer involution rows:", outer_rows)
print("All J2^5 matches:", all_matches)
print("Outer J2^5 matches:", outer_matches)
for rep in data["representations"]:
    print(rep["repname"], "restricts as", rep["m22_restriction_matches"])
    for row in rep["involution_classes"]:
        print(
            "  outer=", row["outer"],
            "class_size=", row["class_size"],
            "rank(g-I)=", row["rank_g_minus_i"],
            "fixdim=", row["fixed_dimension"],
            "J2^5=", row["matches_J2x5"],
        )
PY
