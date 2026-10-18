#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json

from pathlib import Path


SAFE = {
    "CANONICAL_EXACT",
    "CANONICAL_SIGNATURE",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--receipts",
        default=".dashi/round-stranded/lineage-receipts.jsonl",
    )
    ap.add_argument(
        "--out",
        default=".dashi/round-stranded/archive-plan.json",
    )
    args = ap.parse_args()

    receipts = [
        json.loads(line)
        for line in Path(args.receipts).read_text().splitlines()
        if line.strip()
    ]

    safe = []
    blocked = []

    for receipt in receipts:
        bad = [
            candidate
            for candidate in receipt["candidates"]
            if candidate["disposition"] not in SAFE
        ]

        item = {
            "leaf": receipt["leaf"],
            "family": receipt["family"],
            "candidate_count": receipt["candidate_count"],
            "blocking_candidate_count": len(bad),
            "blocking_record_ids": [
                candidate["record_id"] for candidate in bad
            ],
        }

        if bad:
            blocked.append(item)
        else:
            safe.append(item)

    report = {
        "schema_version": 1,
        "policy": "proposal_only_no_files_are_moved",
        "archive_safe_lineages": safe,
        "blocked_lineages": blocked,
        "safe_count": len(safe),
        "blocked_count": len(blocked),
    }

    Path(args.out).write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "safe": len(safe),
                "blocked": len(blocked),
                "output": args.out,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
