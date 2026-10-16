from __future__ import annotations

from pathlib import Path
import sqlite3
from typing import Any

from .checker import Checker


def repository_inventory_coverage(root: Path, conn: sqlite3.Connection) -> dict[str, Any]:
    """Report completeness of the canonical preflight-produced Agda inventory."""

    root = root.resolve()
    producer_row = conn.execute(
        "SELECT value FROM repository_meta WHERE key='inventory_producer'"
    ).fetchone()
    producer = str(producer_row[0]) if producer_row is not None else ""
    if producer != "agda-preflight":
        return {
            "available": False,
            "complete": False,
            "state": "not-native",
            "producer": producer or None,
            "missing": [],
            "extra": [],
            "stale": [],
            "parse_errors": [],
        }

    expected_paths = {
        path.resolve().relative_to(root).as_posix()
        for path in Checker(root).repository_agda_files()
    }
    rows = conn.execute(
        "SELECT path, mtime_ns, size FROM repo_files WHERE language='agda'"
    ).fetchall()
    indexed = {str(row[0]): row for row in rows}
    missing = sorted(expected_paths - set(indexed))
    extra = sorted(set(indexed) - expected_paths)
    stale = []
    for relative in sorted(expected_paths & set(indexed)):
        path = root / relative
        try:
            stat = path.stat()
        except OSError:
            stale.append(relative)
            continue
        row = indexed[relative]
        if int(row[1]) != stat.st_mtime_ns or int(row[2]) != stat.st_size:
            stale.append(relative)
    parse_errors = [
        {"path": str(row[0]), "error": str(row[1] or "parse failure")}
        for row in conn.execute(
            "SELECT path, error FROM repo_inventory_receipts WHERE parsed=0 ORDER BY path"
        )
    ]
    complete = not missing and not extra and not stale and not parse_errors
    return {
        "available": True,
        "complete": complete,
        "state": "complete" if complete else "stale-or-incomplete",
        "producer": producer,
        "indexed_files": len(indexed),
        "repository_files": len(expected_paths),
        "missing": missing[:100],
        "missing_truncated": len(missing) > 100,
        "extra": extra[:100],
        "extra_truncated": len(extra) > 100,
        "stale": stale[:100],
        "stale_truncated": len(stale) > 100,
        "parse_errors": parse_errors[:100],
        "parse_errors_truncated": len(parse_errors) > 100,
    }
