#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build
gap -q scripts/m22d2_276_ten_factor_identification_screen.g

test -s build/m22d2_276_ten_factor_identification_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/m22d2_276_ten_factor_identification_screen.json")
data = json.loads(p.read_text())


def gf2_rank(rows):
    rows = [sum((int(x) & 1) << i for i, x in enumerate(row)) for row in rows]
    rank = 0
    col = 0
    while rows and col < 10000:
        pivot = next((j for j in range(rank, len(rows)) if (rows[j] >> col) & 1), None)
        if pivot is None:
            col += 1
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and ((rows[j] >> col) & 1):
                rows[j] ^= rows[rank]
        rank += 1
        col += 1
        if rank == len(rows):
            break
    return rank


def permute_row(row, perm):
    out = [0] * len(row)
    for i, bit in enumerate(row):
        out[perm[i] - 1] = bit
    return out


assert data["m24_order"] == 244823040
assert data["m22d2_order"] == 887040
assert data["dimension"] == 276
assert data["dimension_sum"] == 276
assert data["composition_series_dimensions"][0] == 0
assert data["composition_series_dimensions"][-1] == 276
assert len(data["composition_series_dimensions"]) == len(data["factor_dimensions"]) + 1
assert [b-a for a,b in zip(data["composition_series_dimensions"], data["composition_series_dimensions"][1:])] == data["factor_dimensions"]
assert data["ten_factor_count"] == data["factor_dimensions"].count(10)
assert len(data["ten_factor_atlasrep_matches"]) == data["ten_factor_count"]
assert data["ten_factor_count"] > 0, "M22:2 duad-276 must expose at least one 10d factor"
for labels in data["ten_factor_atlasrep_matches"]:
    assert labels, "every 10d M22:2 factor must identify with an AtlasRep 10d module"
assert data["every_ten_factor_identified"] is True

lo = data["selected_lower_basis"]
hi = data["selected_upper_basis"]
ld = data["selected_lower_dimension"]
ud = data["selected_upper_dimension"]
assert ud - ld == 10
assert len(lo) == ld and len(hi) == ud
assert all(len(row) == 276 for row in lo + hi)
assert gf2_rank(lo) == ld
assert gf2_rank(hi) == ud
assert gf2_rank(hi + lo) == ud, "N must lie in S"

# Independently verify the emitted subspaces are invariant under each ambient
# M22:2 permutation generator.
for perm in data["ambient_m22d2_generator_permutations"]:
    assert len(perm) == 276 and sorted(perm) == list(range(1,277))
    for basis in (lo, hi):
        r = gf2_rank(basis)
        for row in basis:
            assert gf2_rank(basis + [permute_row(row, perm)]) == r

qgens = data["selected_quotient_generators"]
assert qgens, "quotient generator matrices missing"
for m in qgens:
    assert len(m) == 10 and all(len(row) == 10 for row in m)
    assert gf2_rank(m) == 10

assert data["selected_factor_atlasrep_matches"]
assert data["selected_outer_J2x5_match_count"] > 0
assert any(
    row["matches_J2x5"] is True
    and row["rank_g_minus_i"] == 5
    and row["fixed_dimension"] == 5
    and row["square_zero"] is True
    for row in data["selected_outer_involution_rows"]
)
assert data["finite_duad_same_quotient_Bprime_Cprime_paid"] is True
assert data["actual_2b_tate_stable_subquotient_identified"] is False

print("M22:2 duad-276 factor dimensions:", data["factor_dimensions"])
print("composition-series dimensions:", data["composition_series_dimensions"])
print("10d factor count:", data["ten_factor_count"])
print("10d AtlasRep matches:", data["ten_factor_atlasrep_matches"])
print("selected N<=S dimensions:", ld, "<=", ud)
print("selected quotient Atlas matches:", data["selected_factor_atlasrep_matches"])
print("selected quotient outer J2^5 matches:", data["selected_outer_J2x5_match_count"])
print("finite duad SAME-QUOTIENT B'+C': PASS")
print("actual Tate stable subquotient: intentionally still false")
PY
