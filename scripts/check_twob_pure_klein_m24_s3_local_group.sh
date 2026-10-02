#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build

gap -q scripts/twob_pure_klein_m24_s3_local_group.g

test -s build/twob_pure_klein_m24_s3_local_group.json

python3 - <<'PY'
import json
from pathlib import Path

data = json.loads(Path(
    "build/twob_pure_klein_m24_s3_local_group.json"
).read_text())

assert data["atlas_group_name"] == "2^(2+11+22).(M24xS3)"
assert data["group_order"] == 50472333605150392320
assert data["permutation_degree"] == 294912
assert data["first_block_count"] == 147456
assert data["first_kernel_order"] == 8192
assert data["second_block_count"] == 72
assert data["m24xs3_quotient_order"] == 244823040 * 6
assert set(data["block_seed_sizes"]) == {3,24}
assert data["m24_block_orbit_degree"] == 24
assert data["m24_factor_order"] == 244823040
assert data["s3_block_orbit_degree"] == 3
assert data["s3_factor_order"] == 6
assert data["joint_kernel_order"] == 1
assert data["m24_factor_isomorphic"] is True
assert data["s3_factor_isomorphic"] is True
assert data["actual_2b_tate_action_identified"] is False
assert data["completion10_subquotient_identified"] is False

print("2B-pure local quotient verified: M24 x S3")
PY
