#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from _stranded_common import connect
from _round_package_extraction import classify_packages, load_targets, write_receipts
from cluster_ns_round_packages import cluster_packages


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default="config/ns-round-extraction-targets.json")
    ap.add_argument("--out")
    args = ap.parse_args()

    cfg = load_targets(Path(args.config))
    conn = connect(Path(args.db))
    packages = cluster_packages(conn, cfg)
    rows = classify_packages(conn, cfg, packages)
    out = Path(args.out or cfg["outputs"]["receipts"])
    write_receipts(rows, out)

    counts = defaultdict(int)
    prefixes = defaultdict(int)
    for row in rows:
        counts[row["disposition"]] += 1
        prefixes[row.get("domain", "")] += 1

    print(
        json.dumps(
            {
                "package_count": len(rows),
                "dispositions": dict(sorted(counts.items())),
                "domains": dict(sorted(prefixes.items())),
                "output": str(out),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
