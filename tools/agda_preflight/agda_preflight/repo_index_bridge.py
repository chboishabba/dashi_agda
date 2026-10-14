from __future__ import annotations

import json
from pathlib import Path
import sqlite3
from typing import Optional

from .discovery import classify_surface_role


EXPECTED_SCHEMA = "2.0.0"
DEFAULT_PATH = Path(".repo-index/index.sqlite3")
_IGNORED_PARTS = {
    ".git", ".repo-index", ".pytest_cache", ".venv", ".venv-fluid",
    ".codex_skill_work", "__pycache__", "build", "dist", "node_modules",
    "outputs", "monster", "cubical", "temp-DOWNLOADED",
}
_ALLOWED_TOPLEVEL = {"DASHI", "Docs", "Kernel", "Verification"}
_ALLOWED_DOCS_SUBTREES = {"support", "roadmaps"}


def _allowed(path: Path) -> bool:
    parts = path.parts
    if not parts or any(part in _IGNORED_PARTS for part in parts):
        return False
    if len(parts) > 1 and parts[0] not in _ALLOWED_TOPLEVEL:
        return False
    if len(parts) > 1 and parts[0] == "Docs" and parts[1] not in _ALLOWED_DOCS_SUBTREES:
        return False
    return path.suffix in {".agda", ".md"}


def _json(value: str, default):
    try:
        return json.loads(value)
    except (TypeError, ValueError, json.JSONDecodeError):
        return default


class RepoIndexReader:
    """Read-only bridge to the existing repo-wide discovery index."""

    def __init__(self, root: Path, path: Optional[Path] = None) -> None:
        self.root = root.resolve()
        chosen = path or DEFAULT_PATH
        self.path = chosen if chosen.is_absolute() else self.root / chosen
        self.connection = None
        if self.path.exists():
            uri = "file:{}?mode=ro".format(self.path.resolve().as_posix())
            self.connection = sqlite3.connect(uri, uri=True)
            self.connection.row_factory = sqlite3.Row

    @property
    def available(self) -> bool:
        return self.connection is not None

    def close(self) -> None:
        if self.connection is not None:
            self.connection.close()
            self.connection = None

    def __enter__(self) -> "RepoIndexReader":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    def _schema(self) -> Optional[str]:
        if self.connection is None:
            return None
        try:
            row = self.connection.execute(
                "SELECT value FROM meta WHERE key='schema_version'"
            ).fetchone()
        except sqlite3.DatabaseError:
            return None
        return str(row["value"]) if row is not None else None

    def _row(self, row: sqlite3.Row) -> dict:
        module = row["module"] or ""
        return {
            "symbol_id": row["symbol_id"],
            "qualified_name": row["symbol_id"],
            "name": row["name"],
            "kind": row["kind"],
            "language": row["language"],
            "module_name": module,
            "module": module,
            "path": row["file"],
            "file": row["file"],
            "line_start": int(row["line_start"]),
            "line_end": int(row["line_end"]),
            "status": _json(row["status_json"], {}),
            "tags": _json(row["tags_json"], []),
            "requirements": _json(row["requirements_json"], {}),
            "surface_role": classify_surface_role(module or row["symbol_id"]),
            "inventory_source": "repo-index",
        }

    def search_symbols(
        self,
        query: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> list[dict]:
        if self.connection is None or not query.strip():
            return []
        q = query.strip()
        history_clause = "" if include_history else "AND module NOT LIKE '%Round%'"
        try:
            rows = self.connection.execute(
                """
                SELECT * FROM symbols
                WHERE (symbol_id = ? OR name = ? OR symbol_id LIKE ? OR name LIKE ?)
                  AND language = 'agda'
                  {history_clause}
                ORDER BY
                  CASE WHEN symbol_id = ? THEN 0 WHEN name = ? THEN 1
                       WHEN symbol_id LIKE ? THEN 2 ELSE 3 END,
                  length(symbol_id), symbol_id
                LIMIT ?
                """.format(history_clause=history_clause),
                (q, q, "%" + q + "%", "%" + q + "%", q, q, "%" + q + "%", limit),
            ).fetchall()
        except sqlite3.DatabaseError:
            return []
        return [self._row(row) for row in rows]

    def all_agda_symbols(self, *, include_history: bool = True) -> list[dict]:
        if self.connection is None:
            return []
        clause = "" if include_history else "AND module NOT LIKE '%Round%'"
        try:
            rows = self.connection.execute(
                "SELECT * FROM symbols WHERE language='agda' {} ORDER BY symbol_id".format(clause)
            ).fetchall()
        except sqlite3.DatabaseError:
            return []
        return [self._row(row) for row in rows]

    def object_detail(self, symbol_id: str) -> dict:
        if self.connection is None:
            return {"symbol": None, "refs": []}
        row = self.connection.execute(
            "SELECT * FROM symbols WHERE symbol_id = ? LIMIT 1", (symbol_id,)
        ).fetchone()
        if row is None:
            return {"symbol": None, "refs": []}
        refs = self.connection.execute(
            """
            SELECT from_symbol, to_symbol, ref_kind, file, line, snippet
            FROM refs WHERE to_symbol = ? OR from_symbol = ?
            ORDER BY file, line LIMIT 200
            """,
            (symbol_id, symbol_id),
        ).fetchall()
        return {"symbol": self._row(row), "refs": [dict(item) for item in refs]}

    def coverage_status(self) -> dict:
        if self.connection is None:
            return {
                "available": False,
                "schema_version": None,
                "complete": False,
                "state": "missing",
                "missing": [],
                "stale": [],
            }
        schema = self._schema()
        try:
            indexed_rows = self.connection.execute(
                "SELECT path, mtime_ns, size FROM files"
            ).fetchall()
        except sqlite3.DatabaseError:
            return {
                "available": True,
                "schema_version": schema,
                "complete": False,
                "state": "invalid",
                "missing": [],
                "stale": [],
            }
        indexed = {str(row["path"]): row for row in indexed_rows}
        repo_paths = set()
        for path in self.root.rglob("*"):
            if not path.is_file():
                continue
            try:
                relative = path.resolve().relative_to(self.root).as_posix()
            except ValueError:
                continue
            rel_path = Path(relative)
            if _allowed(rel_path):
                repo_paths.add(relative)
        missing = sorted(repo_paths - set(indexed))
        extra = sorted(set(indexed) - repo_paths)
        stale = []
        for relative in sorted(repo_paths & set(indexed)):
            path = self.root / relative
            try:
                stat = path.stat()
            except OSError:
                stale.append(relative)
                continue
            row = indexed[relative]
            if int(row["mtime_ns"]) != stat.st_mtime_ns or int(row["size"]) != stat.st_size:
                stale.append(relative)
        complete = schema == EXPECTED_SCHEMA and not missing and not extra and not stale
        return {
            "available": True,
            "schema_version": schema,
            "complete": complete,
            "state": "complete" if complete else "stale-or-incomplete",
            "indexed_files": len(indexed),
            "repository_files": len(repo_paths),
            "missing": missing[:100],
            "missing_truncated": len(missing) > 100,
            "extra": extra[:100],
            "extra_truncated": len(extra) > 100,
            "stale": stale[:100],
            "stale_truncated": len(stale) > 100,
        }
