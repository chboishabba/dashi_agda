#!/usr/bin/env python3
"""Attach exact QID/OEIS occurrences to already indexed Agda declarations.

Uses the canonical preflight DB, its source file spans and existing jmd_world
tables. No separate index. No inference from Wikipedia topic names, numbers,
nearby comments, or whole-file proximity. All edges are discovery-only.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import sqlite3
from pathlib import Path

QID = re.compile(r"(?<![A-Za-z0-9])Q[1-9][0-9]*(?![0-9])")
OEIS = re.compile(r"(?<![A-Za-z0-9])A[0-9]{6}(?![0-9])")


def attach(root: Path, conn: sqlite3.Connection):
    matches = 0
    unmatched = 0
    queries = """SELECT w.source_key, s.file, s.line_start, s.line_end
       FROM jmd_world_sources w JOIN repo_symbols s
         ON s.symbol_id=w.declaration
       WHERE w.input_kind='agda' AND s.language='agda'
       ORDER BY w.source_key"""
    files = {}
    for key, file, start, end in conn.execute(queries).fetchall():
        path = (root / file).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            unmatched += 1
            continue
        if file not in files:
            raw = path.read_bytes()
            files[file] = (raw.decode("utf-8", "replace").splitlines(),
                           hashlib.sha256(raw).hexdigest())
        lines, digest = files[file]
        if start < 1 or end < start or end > len(lines):
            unmatched += 1
            continue
        # AST-owned exact declaration span only, never module-wide header.
        text = "\n".join(lines[start-1:end])
        coords = QID.findall(text) + OEIS.findall(text)
        for coord in sorted(set(coords)):
            # Coordinate/provenance is separate from mathematical identity.
            prov = f"agda-source-span:{file}:{start}-{end}:sha256:{digest}"
            conn.execute("""INSERT OR IGNORE INTO jmd_world_external_coordinates
            (source_key,coordinate,provenance) VALUES(?,?,?)""",
                         (key,coord,prov))
            matches += 1
    return {"source_span_external_coordinates":matches,
            "source_spans_not_read":unmatched,
            "theorem_equivalences_established":0}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--agda-root",type=Path,required=True)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    args=p.parse_args()
    if not args.database.is_file():
        p.error("Run dashi-repo index and the JMD world reconciliation first")
    conn=sqlite3.connect(args.database)
    try:
        with conn:
            result=attach(args.agda_root.resolve(),conn)
        import json
        print(json.dumps(result,indent=2))
    finally:
        conn.close()


if __name__=="__main__":
    main()
