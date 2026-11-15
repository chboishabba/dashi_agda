#!/usr/bin/env python3
"""Large-corpus streaming ORIGINAL-first-link behavioural-port census.

Input is operator-supplied JSONL, one revisioned page per line with exact
(pageid, oldid, title, wikitext, wikitext_sha256). A supplied whole-file
SHA256 and individual wikitext digests are checked. The original 2016 dump,
original author-run parser and page-redirect identity are NOT authenticated
just because this tool successfully analyses the supplied corpus.

Uses one local SQLite *analytic scratch index*, not a new service, S29
database or promoted Wikidata source. Every out-of-corpus edge remains an
unresolved target, never a dead-end or a globally absent page.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sqlite3
import sys
from typing import Any

from ibrahim_author_parser_port import (
    SOURCE_BLOB, reference_first_qualifying_link,
)

_SCHEMA = (
    "CREATE TABLE pages (title TEXT PRIMARY KEY, pageid INTEGER NOT NULL UNIQUE, "
    "oldid INTEGER NOT NULL, first_target TEXT, wikitext_sha256 TEXT NOT NULL)",
    "CREATE TABLE outcomes (title TEXT PRIMARY KEY REFERENCES pages(title), "
    "kind TEXT NOT NULL, root TEXT NOT NULL, distance INTEGER NOT NULL, "
    "period INTEGER NOT NULL)",
)


def _pairs(items):
    row = {}
    for k, v in items:
        if k in row:
            raise ValueError("duplicate corpus JSON key: " + k)
        row[k] = v
    return row


def index_corpus(*, jsonl: Path, db: sqlite3.Connection,
                 expected_jsonl_sha256: str,
                 max_line_bytes: int = 64 * 1024 * 1024,
                 max_pages: int = 10_000_000) -> tuple[int, str]:
    if (type(expected_jsonl_sha256) is not str or len(expected_jsonl_sha256) != 64
            or any(c not in "0123456789abcdef" for c in expected_jsonl_sha256)):
        raise ValueError("complete independently supplied JSONL SHA256 required")
    for statement in _SCHEMA:
        db.execute(statement)
    h = sha256()
    count = 0
    with jsonl.open("rb") as stream:
        while True:
            # read a bounded line; never materialise a multi-GiB malformed row
            line = stream.readline(max_line_bytes + 1)
            if not line:
                break
            if not 0 < len(line) <= max_line_bytes:
                raise ValueError("empty/oversized corpus JSONL row")
            h.update(line)
            row = json.loads(line.decode("utf-8"), object_pairs_hook=_pairs)
            if type(row) is not dict:
                raise ValueError("corpus JSONL row must be an object")
            pageid, oldid, title, text, digest = (
                row.get("pageid"), row.get("oldid"), row.get("title"),
                row.get("wikitext"), row.get("wikitext_sha256"))
            if (type(pageid) is not int or pageid <= 0
                    or type(oldid) is not int or oldid <= 0
                    or type(title) is not str or not title
                    or type(text) is not str
                    or type(digest) is not str
                    or sha256(text.encode("utf-8")).hexdigest() != digest):
                raise ValueError("corpus original pageid/oldid/wikitext raw hash mismatch")
            first = reference_first_qualifying_link(text)
            target = first["selected_target"] if first is not None else None
            db.execute(
                "INSERT INTO pages(title,pageid,oldid,first_target,wikitext_sha256) "
                "VALUES (?,?,?,?,?)", (title, pageid, oldid, target, digest))
            count += 1
            if count > max_pages:
                raise ValueError("operator maximum page count exceeded")
    actual = h.hexdigest()
    if actual != expected_jsonl_sha256:
        raise ValueError("entire input corpus JSONL hash differs from supplied SHA256")
    db.commit()
    return count, actual


def classify_one(db: sqlite3.Connection, start: str) -> None:
    # O(length until cached/cycle) original-title traversal, no in-memory
    # full-corpus graph. Final classifications are cached in SQLite.
    chain: list[str] = []
    where: dict[str, int] = {}
    cursor = start
    while True:
        cached = db.execute(
            "SELECT kind,root,distance,period FROM outcomes WHERE title=?",
            (cursor,)).fetchone()
        if cached is not None:
            kind, root, distance, period = cached
            for title in reversed(chain):
                distance += 1
                db.execute("INSERT INTO outcomes VALUES (?,?,?,?,?)",
                           (title, kind, root, distance, period))
            return
        if cursor in where:
            entry = where[cursor]
            nodes = chain[entry:]
            root = min(nodes)
            length = len(nodes)
            for node in nodes:
                db.execute("INSERT INTO outcomes VALUES (?,?,?,?,?)",
                           (node, "cycle", root, 0, length))
            dist = 0
            for node in reversed(chain[:entry]):
                dist += 1
                db.execute("INSERT INTO outcomes VALUES (?,?,?,?,?)",
                           (node, "cycle", root, dist, length))
            return
        item = db.execute("SELECT first_target FROM pages WHERE title=?",
                          (cursor,)).fetchone()
        if item is None:
            # A selected target is not among the input rows. It is unresolved,
            # and its exact original title must survive unaltered.
            distance = 0
            for title in reversed(chain):
                distance += 1
                db.execute("INSERT INTO outcomes VALUES (?,?,?,?,?)",
                           (title, "unresolved_target", cursor, distance, 0))
            return
        target = item[0]
        where[cursor] = len(chain)
        chain.append(cursor)
        if target is None:
            # No actual original first qualified link from this source row.
            distance = 0
            for title in reversed(chain):
                db.execute("INSERT INTO outcomes VALUES (?,?,?,?,?)",
                           (title, "dead_end", cursor, distance, 0))
                distance += 1
            return
        cursor = target


def classify_all(db: sqlite3.Connection) -> dict[str, Any]:
    for (title,) in db.execute("SELECT title FROM pages ORDER BY pageid"):
        if db.execute("SELECT 1 FROM outcomes WHERE title=?", (title,)).fetchone() is None:
            classify_one(db, title)
    db.commit()
    count = db.execute("SELECT COUNT(*) FROM pages").fetchone()[0]
    recorded = db.execute("SELECT COUNT(*) FROM outcomes").fetchone()[0]
    if count != recorded:
        raise ValueError("partial census failed to classify every original input row")
    kinds = {row[0]: row[1] for row in db.execute(
        "SELECT kind,COUNT(*) FROM outcomes GROUP BY kind")}
    cycles = [
        {"root": row[0], "period": row[1], "basin_size": row[2]}
        for row in db.execute(
            "SELECT root,period,COUNT(*) FROM outcomes WHERE kind='cycle' "
            "GROUP BY root,period ORDER BY root")
    ]
    return {"input_pages": count, "outcome_counts": kinds, "observed_cycles": cycles,
            "total_distinct_cycle_basins": len(cycles)}


def run_census(*, jsonl: Path, index_path: Path, output: Path,
               expected_jsonl_sha256: str) -> dict[str, Any]:
    if index_path.exists() or index_path.is_symlink():
        raise ValueError("refuse overwrite existing local corpus index")
    if output.exists() or output.is_symlink():
        raise ValueError("refuse overwrite existing census receipt")
    # sqlite will create a local analytic index only; not production S29.
    with sqlite3.connect(index_path) as db:
        pages, matched = index_corpus(jsonl=jsonl, db=db,
                                     expected_jsonl_sha256=expected_jsonl_sha256)
        totals = classify_all(db)
    result = {
        "version": "dashi.wikipedia.partial_original_first_link_census.v1",
        "input_jsonl_raw_sha256_matched_supplied_pin": matched,
        "input_revisioned_page_count": pages,
        "reference_parser_source_blob": SOURCE_BLOB,
        **totals,
        "every_declared_input_page_classified": True,
        "every_wikipedia_page_globally_enumerated": False,
        "historical_2016_dump_originality_independently_proved": False,
        "original_author_executable_parser_ran": False,
        "redirects_and_title_equivalence_independently_proved": False,
        "out_of_corpus_missing_targets_are_negative_evidence": False,
        "source_support_paid": False,
        "edit_authority": False,
    }
    with output.open("x", encoding="utf-8") as file:
        file.write(json.dumps(result, sort_keys=True, indent=2) + "\n")
    return result


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input-jsonl", type=Path, required=True)
    p.add_argument("--expected-jsonl-sha256", required=True)
    p.add_argument("--local-index", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    try:
        receipt = run_census(jsonl=args.input_jsonl, index_path=args.local_index,
                             output=args.output,
                             expected_jsonl_sha256=args.expected_jsonl_sha256)
        print(json.dumps(receipt, sort_keys=True, indent=2))
        return 0
    except (OSError, ValueError, TypeError, sqlite3.DatabaseError,
            UnicodeDecodeError, json.JSONDecodeError) as exc:
        print(json.dumps({"status": "blocked", "reason": str(exc),
                          "source_support_paid": False}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
