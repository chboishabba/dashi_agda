#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/test_generate_ns_luo_submission_audit.py

REPORT="$(mktemp --suffix=.ns-luo-submission-audit.json)"
trap 'rm -f "$REPORT"' EXIT

python3 scripts/generate_ns_luo_submission_audit.py \
  --strict \
  --output "$REPORT"

python3 - "$REPORT" <<'PY'
import json
import sys
from pathlib import Path

report_path = Path(sys.argv[1])
payload = json.loads(report_path.read_text(encoding="utf-8"))

if payload["files_without_module_header"]:
    raise SystemExit(
        "Luo audit found files without a module header: "
        + ", ".join(payload["files_without_module_header"])
    )

required_boundaries = ("finite", "infinite", "rational", "real")
missing = [
    name for name in required_boundaries
    if payload["boundary_summary"].get(name, 0) == 0
]
if missing:
    raise SystemExit(
        "Luo audit did not expose required boundary vocabulary: "
        + ", ".join(missing)
    )

print(
    "strict Luo submission audit passed: "
    f"{payload['file_count']} files, "
    f"{payload['declaration_count']} declarations, "
    f"{len(payload['dependency_edges'])} dependency edges"
)
PY
