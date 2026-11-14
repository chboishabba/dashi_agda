#!/usr/bin/env python3
"""Fail-closed, read-only check of the YM canonical 219-field A-I inventory.

It checks literal record field names/order, class counts, and Git blob
identities against source Agda. It explicitly does NOT verify any theorem
inhabitation, Clay endpoint, physical Haar, OS positivity or typechecking.

Usage: python3 scripts/check_ym_219_field_inventory.py [repo-root]
"""
from collections import Counter
from hashlib import sha1
import json
from pathlib import Path
import re
import sys

REGISTRY = Path("Docs/roadmaps/YMClaySubmission219FieldInventory20261103.json")
RECORD = re.compile(r"(?m)^record\s+([A-Za-z0-9_]+)\b")
FIELD = re.compile(r"(?m)^ {4}([A-Za-z][A-Za-z0-9_′-]*)\s*:\s*")
EXPECTED = dict(A=58, B=56, C=13, D=10, E=13, F=20, G=21, H=15, I=13)


def git_blob_sha(data: bytes) -> str:
    return sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def parse_records(source: str):
    matches = list(RECORD.finditer(source))
    result = {}
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(source)
        result[match.group(1)] = FIELD.findall(source[match.start():end])
    return result


def verify(root: Path):
    registry = json.loads((root / REGISTRY).read_text(encoding="utf-8"))
    assert registry["schema"] == "DASHI.YM.full-submission-field-inventory.v1"
    rows = registry["rows"]
    assert registry["formal_submission_count"] == len(rows) == 219
    assert registry["theorem_spine_count"] == 191
    assert registry["foundation_and_gauge_count"] == 28
    assert registry["lane_counts"] == EXPECTED

    src_paths = sorted({r["source_path"] for r in rows})
    sources = {}
    for path in src_paths:
        data = (root / path).read_bytes()
        sources[path] = (git_blob_sha(data), parse_records(data.decode("utf-8")))

    indices = Counter()
    groups = {}
    for row in rows:
        lane = row["id"].split("-")[1][0]
        assert lane in EXPECTED
        indices[lane] += 1
        assert row["id"] == f"YM-{lane}{indices[lane]:03d}", row["id"]
        assert row["individual_discharge"] == "NOT_AUDITED", row["id"]
        assert row["is_clay_proof"] is False, row["id"]
        git_sha, parsed = sources[row["source_path"]]
        assert row["source_blob_sha"] == git_sha, row["id"]
        assert row["contract_record"] in parsed, row["id"]
        key = (row["source_path"], row["contract_record"])
        groups.setdefault(key, []).append(row["field"])

    for (path, record), fields in groups.items():
        assert fields == sources[path][1][record], (path, record)

    assert dict(indices) == EXPECTED, indices
    print("YM exact 219-field inventory: PASS literal source/record/count/blob check")
    print("  lanes:", dict(indices))
    print("  source files:", src_paths)
    print("  individual proof discharge: NOT AUDITED; kernel: NOT CHECKED")
    return 0


if __name__ == "__main__":
    home = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
    try:
        sys.exit(verify(home))
    except (AssertionError, OSError, KeyError, ValueError) as error:
        print("YM 219-field source inventory: STALE / FAIL:", repr(error), file=sys.stderr)
        sys.exit(1)
