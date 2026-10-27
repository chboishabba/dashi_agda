#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from _stranded_common import connect
from _round_package_extraction import (
    BASE_ARCHIVE_STATUS as ARCHIVE_STATUS,
    build_nonround_indexes,
    classify_package,
    classify_packages,
    write_receipts as _write_receipts,
)
from cluster_ym_round_packages import cluster_packages, load_targets


def write_receipts(rows: list[dict], out: Path, max_matches: int = 10) -> None:
    """Compatibility writer with additive evidence-count fields.

    Classification already applies the configured sample cap.  This wrapper also
    handles hand-built fixture rows from the legacy pytest surface.
    """
    materialized: list[dict] = []
    for row in rows:
        item = dict(row)
        matches = list(item.get("nonround_matches", []))
        item.setdefault("nonround_match_count", len(matches))
        if len(matches) > max_matches:
            item["nonround_matches"] = matches[:max_matches]
        item.setdefault(
            "nonround_matches_truncated",
            item["nonround_match_count"] > len(item.get("nonround_matches", [])),
        )
        item["archive_status"] = ARCHIVE_STATUS[item["disposition"]]
        if item["disposition"] == "STATUS_ONLY":
            item["selected_canonical_owner"] = None
        materialized.append(item)
    _write_receipts(materialized, out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default="config/ym-round-extraction-targets.json")
    ap.add_argument("--out")
    args = ap.parse_args()

    cfg = load_targets(Path(args.config))
    conn = connect(Path(args.db))
    packages = cluster_packages(conn, cfg)
    rows = classify_packages(conn, cfg, packages)
    out = Path(args.out or cfg["outputs"]["receipts"])
    write_receipts(rows, out, int(cfg.get("nonround_match_sample_limit", 10)))
    counts = defaultdict(int)
    for row in rows:
        counts[row["disposition"]] += 1
    print(
        json.dumps(
            {
                "package_count": len(rows),
                "dispositions": dict(sorted(counts.items())),
                "output": str(out),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
