#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from _stranded_common import connect
from _round_package_extraction import cluster_packages, load_targets, write_jsonl


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default="config/ns-round-extraction-targets.json")
    ap.add_argument("--out")
    args = ap.parse_args()

    cfg = load_targets(Path(args.config))
    conn = connect(Path(args.db))
    rows = cluster_packages(conn, cfg)
    out = Path(args.out or cfg["outputs"]["clusters"])
    write_jsonl(rows, out)
    print(json.dumps({"package_count": len(rows), "output": str(out)}, indent=2))


if __name__ == "__main__":
    main()
