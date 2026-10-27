from __future__ import annotations

import sqlite3
from typing import Dict, List, Tuple


AnnotationSnapshot = Dict[str, dict]


def capture_repository_annotations(conn: sqlite3.Connection) -> AnnotationSnapshot:
    result: AnnotationSnapshot = {}
    try:
        symbol_ids = [str(row[0]) for row in conn.execute("SELECT symbol_id FROM repo_symbols")]
    except sqlite3.DatabaseError:
        return result
    for symbol_id in symbol_ids:
        tags = [
            str(row[0])
            for row in conn.execute(
                "SELECT tag FROM repo_symbol_tags WHERE symbol_id=? ORDER BY tag",
                (symbol_id,),
            )
        ]
        requirements = [
            tuple(str(value) for value in row)
            for row in conn.execute(
                """
                SELECT requirement_class, requirement_kind, required_symbol, source
                FROM repo_requirements WHERE symbol_id=?
                ORDER BY requirement_class, requirement_kind, required_symbol, source
                """,
                (symbol_id,),
            )
        ]
        if tags or requirements:
            result[symbol_id] = {
                "tags": tags,
                "requirements": requirements,
            }
    return result


def restore_repository_annotations(
    conn: sqlite3.Connection,
    snapshot: AnnotationSnapshot,
) -> int:
    restored = 0
    for symbol_id, payload in snapshot.items():
        if conn.execute(
            "SELECT 1 FROM repo_symbols WHERE symbol_id=?",
            (symbol_id,),
        ).fetchone() is None:
            continue
        for tag in payload.get("tags", ()):
            conn.execute(
                "INSERT OR IGNORE INTO repo_symbol_tags(symbol_id, tag) VALUES(?, ?)",
                (symbol_id, tag),
            )
            restored += 1
        for requirement in payload.get("requirements", ()):
            requirement_class, requirement_kind, required_symbol, source = requirement
            conn.execute(
                """
                INSERT OR IGNORE INTO repo_requirements(
                    symbol_id, requirement_class, requirement_kind,
                    required_symbol, source
                ) VALUES(?, ?, ?, ?, ?)
                """,
                (
                    symbol_id,
                    requirement_class,
                    requirement_kind,
                    required_symbol,
                    source,
                ),
            )
            restored += 1
    conn.commit()
    return restored
