from __future__ import annotations

from pathlib import Path
import sqlite3
from typing import Optional

from .discovery import classify_surface_role
from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    LEGACY_REPO_INDEX,
    ensure_repository_schema,
    sync_legacy_repo_index,
)


EXPECTED_SCHEMA = "2.0.0"
DEFAULT_PATH = DEFAULT_REPOSITORY_DB
_IGNORED_PARTS = {
    ".git", ".repo-index", ".dashi", ".pytest_cache", ".venv", ".venv-fluid",
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


def _has_table(path: Path, table: str) -> bool:
    if not path.exists():
        return False
    try:
        conn = sqlite3.connect(path)
        row = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?",
            (table,),
        ).fetchone()
        conn.close()
    except sqlite3.DatabaseError:
        return False
    return row is not None


class RepoIndexReader:
    """Read the normalized repo-wide inventory from the unified SQLite DB.

    Passing an old `.repo-index/index.sqlite3` path remains supported as a
    migration ingress. The reader imports it into `.dashi/repository.sqlite3`
    and then reads only the normalized relational tables.
    """

    def __init__(
        self,
        root: Path,
        path: Optional[Path] = None,
        *,
        connection: Optional[sqlite3.Connection] = None,
    ) -> None:
        self.root = root.resolve()
        self._owns_connection = connection is None
        if connection is not None:
            self.connection = connection
            self.path = Path("<shared-connection>")
            ensure_repository_schema(self.connection)
            return

        explicit = path is not None
        chosen = path or DEFAULT_PATH
        candidate = chosen if chosen.is_absolute() else self.root / chosen
        legacy_default = self.root / LEGACY_REPO_INDEX

        legacy_source: Optional[Path] = None
        if candidate.exists() and not _has_table(candidate, "repo_symbols"):
            if _has_table(candidate, "symbols") and _has_table(candidate, "files"):
                legacy_source = candidate
        elif not candidate.exists() and not explicit and legacy_default.exists():
            legacy_source = legacy_default

        if legacy_source is not None:
            unified = self.root / DEFAULT_REPOSITORY_DB
            unified.parent.mkdir(parents=True, exist_ok=True)
            conn = sqlite3.connect(unified)
            conn.row_factory = sqlite3.Row
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.execute("PRAGMA foreign_keys=ON")
            conn.execute("PRAGMA busy_timeout=5000")
            ensure_repository_schema(conn)
            sync_legacy_repo_index(
                self.root,
                conn,
                legacy_path=legacy_source,
                force=True,
            )
            self.connection = conn
            self.path = unified
            return

        self.path = candidate
        self.connection = None
        if self.path.exists():
            uri = "file:{}?mode=ro".format(self.path.resolve().as_posix())
            self.connection = sqlite3.connect(uri, uri=True)
            self.connection.row_factory = sqlite3.Row

    @property
    def available(self) -> bool:
        if self.connection is None:
            return False
        try:
            row = self.connection.execute("SELECT count(*) FROM repo_files").fetchone()
        except sqlite3.DatabaseError:
            return False
        return bool(row and int(row[0]) > 0)

    def close(self) -> None:
        if self._owns_connection and self.connection is not None:
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
                "SELECT value FROM repository_meta WHERE key='legacy_repo_index_schema'"
            ).fetchone()
        except sqlite3.DatabaseError:
            return None
        return str(row[0]) if row is not None else None

    def _tags(self, symbol_id: str) -> list[str]:
        if self.connection is None:
            return []
        return [
            str(row[0])
            for row in self.connection.execute(
                "SELECT tag FROM repo_symbol_tags WHERE symbol_id=? ORDER BY tag",
                (symbol_id,),
            )
        ]

    def _requirements(self, symbol_id: str) -> dict:
        if self.connection is None:
            return {}
        result: dict[str, list[dict[str, str]]] = {}
        rows = self.connection.execute(
            """
            SELECT requirement_class, requirement_kind, required_symbol, source
            FROM repo_requirements
            WHERE symbol_id=?
            ORDER BY requirement_class, requirement_kind, required_symbol, source
            """,
            (symbol_id,),
        )
        for row in rows:
            result.setdefault(str(row[0]), []).append(
                {
                    "kind": str(row[1]),
                    "symbol": str(row[2]),
                    "source": str(row[3]),
                }
            )
        return result

    def _row(self, row: sqlite3.Row) -> dict:
        module = row["module"] or ""
        symbol_id = str(row["symbol_id"])
        return {
            "symbol_id": symbol_id,
            "qualified_name": symbol_id,
            "name": row["name"],
            "kind": row["kind"],
            "language": row["language"],
            "module_name": module,
            "module": module,
            "path": row["file"],
            "file": row["file"],
            "line_start": int(row["line_start"]),
            "line_end": int(row["line_end"]),
            "status": {
                "promotion": row["promotion"],
                "authority": row["authority"],
                "truth": row["truth"],
                "source": row["source"],
            },
            "tags": self._tags(symbol_id),
            "requirements": self._requirements(symbol_id),
            "surface_role": classify_surface_role(module or symbol_id),
            "inventory_source": "repository-db",
        }

    def search_symbols(
        self,
        query: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> list[dict]:
        if not self.available or not query.strip():
            return []
        q = query.strip()
        history_clause = "" if include_history else "AND module NOT GLOB '*Round[0-9]*'"
        try:
            rows = self.connection.execute(
                """
                SELECT * FROM repo_symbols
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
        if not self.available:
            return []
        clause = "" if include_history else "AND module NOT GLOB '*Round[0-9]*'"
        try:
            rows = self.connection.execute(
                "SELECT * FROM repo_symbols WHERE language='agda' {} ORDER BY symbol_id".format(clause)
            ).fetchall()
        except sqlite3.DatabaseError:
            return []
        return [self._row(row) for row in rows]

    def object_detail(self, symbol_id: str) -> dict:
        if not self.available:
            return {"symbol": None, "refs": []}
        try:
            row = self.connection.execute(
                "SELECT * FROM repo_symbols WHERE symbol_id = ? LIMIT 1", (symbol_id,)
            ).fetchone()
        except sqlite3.DatabaseError:
            return {"symbol": None, "refs": []}
        if row is None:
            return {"symbol": None, "refs": []}
        try:
            refs = self.connection.execute(
                """
                SELECT from_symbol, to_symbol, ref_kind, file, line, snippet
                FROM repo_refs WHERE to_symbol = ? OR from_symbol = ?
                ORDER BY file, line LIMIT 200
                """,
                (symbol_id, symbol_id),
            ).fetchall()
        except sqlite3.DatabaseError:
            refs = []
        return {"symbol": self._row(row), "refs": [dict(item) for item in refs]}

    def coverage_status(self) -> dict:
        if not self.available:
            return {
                "available": False,
                "schema_version": self._schema(),
                "complete": False,
                "state": "missing",
                "missing": [],
                "stale": [],
            }
        schema = self._schema()
        try:
            indexed_rows = self.connection.execute(
                "SELECT path, mtime_ns, size FROM repo_files"
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
        for source_path in self.root.rglob("*"):
            if not source_path.is_file():
                continue
            try:
                relative = source_path.resolve().relative_to(self.root).as_posix()
            except ValueError:
                continue
            rel_path = Path(relative)
            if _allowed(rel_path):
                repo_paths.add(relative)
        missing = sorted(repo_paths - set(indexed))
        extra = sorted(set(indexed) - repo_paths)
        stale = []
        for relative in sorted(repo_paths & set(indexed)):
            source_path = self.root / relative
            try:
                stat = source_path.stat()
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
