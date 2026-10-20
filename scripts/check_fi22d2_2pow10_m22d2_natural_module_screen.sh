#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build
gap -q scripts/fi22d2_2pow10_m22d2_natural_module_screen.g

test -s build/fi22d2_2pow10_m22d2_natural_module_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/fi22d2_2pow10_m22d2_natural_module_screen.json")
data = json.loads(p.read_text())

assert data["fi22d2_order"] == 129123503308800
assert data["maximal_subgroup_order"] == 908328960
assert 129123503308800 // 908328960 == 142155
assert data["normal_kernel_order"] == 1024
assert data["normal_kernel_elementary_abelian"] is True
assert data["quotient_order"] == 887040
assert data["natural_module_dimension"] == 10
assert data["natural_action_group_order"] == 887040
assert data["atlas_m22d2_10d_matches"], "natural 2^10 action must match an Atlas M22:2 10d module"
assert data["outer_involution_rows"], "expected at least one outer involution class"
assert data["outer_J2x5_match_count"] > 0, "natural 2^10 module must expose the outer J2^5 fingerprint"
assert data["finite_source_native_completion10_module_identified"] is True
assert data["actual_2b_tate_same_object_identified"] is False

print("Fi22:2 maximal index:", 142155)
print("Fi22:2 normal 2^10 Atlas matches:", data["atlas_m22d2_10d_matches"])
print("natural action group order:", data["natural_action_group_order"])
print("outer involution rows:", data["outer_involution_rows"])
print("outer J2^5 match count:", data["outer_J2x5_match_count"])
print("finite source-native Completion10 donor: PASS")
print("actual 2B Tate same-object identification: intentionally false")
PY
