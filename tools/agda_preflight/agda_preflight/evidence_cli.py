from __future__ import annotations

import argparse
import json

from .evidence import (
    DIAGNOSTIC_POLICIES,
    EvidenceLevel,
    evidence_name,
)


def _rows():
    rows = []
    for code in sorted(DIAGNOSTIC_POLICIES):
        policy = DIAGNOSTIC_POLICIES[code]
        rows.append(
            {
                "code": code,
                "minimum_evidence": evidence_name(policy.minimum),
                "hard_error_allowed": policy.hard_error_allowed,
                "description": policy.description,
            }
        )
    return rows


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-evidence",
        description="Show evidence requirements for TSAGDA diagnostics.",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument(
        "--level",
        choices=[evidence_name(level) for level in EvidenceLevel],
        help="show only diagnostics requiring this minimum evidence level",
    )
    args = parser.parse_args(argv)

    rows = _rows()
    if args.level:
        rows = [
            row for row in rows
            if row["minimum_evidence"] == args.level
        ]

    if args.json:
        print(json.dumps(rows, indent=2, sort_keys=True))
        return 0

    grouped = {}
    for row in rows:
        grouped.setdefault(row["minimum_evidence"], []).append(row)

    for level in (
        "tree-sitter",
        "dashi-index",
        "agda-scope",
        "agda-typechecker",
    ):
        items = grouped.get(level, [])
        if not items:
            continue
        print(f"{level} ({len(items)})")
        for row in items:
            hard = "hard" if row["hard_error_allowed"] else "advisory"
            print(f"  {row['code']}  {hard}  {row['description']}")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
