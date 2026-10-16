from __future__ import annotations

from collections import defaultdict
from difflib import SequenceMatcher
import json
from pathlib import Path
import re
import sqlite3
from typing import Any, Iterable, Optional


DEFAULT_REPOSITORY_DB = Path(".dashi/repository.sqlite3")
LEGACY_REPO_INDEX = Path(".repo-index/index.sqlite3")
REPO_INVENTORY_SCHEMA = "3"
NARRATIVE_SCHEMA = "1"
_TOKEN_RE = re.compile(r"[A-Za-z0-9_+'-]+")


def ensure_repository_schema(conn: sqlite3.Connection) -> None:
    """Install the shared relational schema used by discovery and history.

    The existing preflight tables remain untouched.  The `repo_*` namespace is
    the normalized successor to the old `.repo-index/index.sqlite3` schema and
    the `narrative_*` namespace replaces the former JSON handoff.
    """

    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS repository_meta (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS repo_files (
            path TEXT PRIMARY KEY,
            language TEXT NOT NULL,
            module TEXT,
            mtime_ns INTEGER NOT NULL,
            size INTEGER NOT NULL,
            sha256 TEXT NOT NULL,
            indexed_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS repo_files_module ON repo_files(module);

        CREATE TABLE IF NOT EXISTS repo_file_imports (
            file TEXT NOT NULL REFERENCES repo_files(path) ON DELETE CASCADE,
            imported_module TEXT NOT NULL,
            line INTEGER NOT NULL DEFAULT 0,
            owner_symbol TEXT,
            PRIMARY KEY(file, imported_module, line)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS repo_file_imports_module
            ON repo_file_imports(imported_module);

        CREATE TABLE IF NOT EXISTS repo_doc_links (
            file TEXT NOT NULL REFERENCES repo_files(path) ON DELETE CASCADE,
            url TEXT NOT NULL,
            PRIMARY KEY(file, url)
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS repo_symbols (
            symbol_id TEXT PRIMARY KEY,
            name TEXT NOT NULL,
            kind TEXT NOT NULL,
            language TEXT NOT NULL,
            module TEXT,
            file TEXT NOT NULL REFERENCES repo_files(path) ON DELETE CASCADE,
            line_start INTEGER NOT NULL,
            line_end INTEGER NOT NULL,
            promotion TEXT NOT NULL DEFAULT 'unknown',
            authority TEXT NOT NULL DEFAULT 'unknown',
            truth TEXT NOT NULL DEFAULT 'unknown',
            source TEXT NOT NULL DEFAULT 'unknown'
        );
        CREATE INDEX IF NOT EXISTS repo_symbols_name ON repo_symbols(name);
        CREATE INDEX IF NOT EXISTS repo_symbols_module ON repo_symbols(module);
        CREATE INDEX IF NOT EXISTS repo_symbols_file ON repo_symbols(file);

        CREATE TABLE IF NOT EXISTS repo_symbol_tags (
            symbol_id TEXT NOT NULL REFERENCES repo_symbols(symbol_id) ON DELETE CASCADE,
            tag TEXT NOT NULL,
            PRIMARY KEY(symbol_id, tag)
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS repo_requirements (
            symbol_id TEXT NOT NULL REFERENCES repo_symbols(symbol_id) ON DELETE CASCADE,
            requirement_class TEXT NOT NULL,
            requirement_kind TEXT NOT NULL,
            required_symbol TEXT NOT NULL,
            source TEXT NOT NULL,
            PRIMARY KEY(
                symbol_id,
                requirement_class,
                requirement_kind,
                required_symbol,
                source
            )
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS repo_mentions (
            file TEXT NOT NULL REFERENCES repo_files(path) ON DELETE CASCADE,
            line INTEGER NOT NULL,
            owner_symbol TEXT,
            token TEXT NOT NULL,
            snippet TEXT NOT NULL,
            source_kind TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS repo_mentions_token ON repo_mentions(token);
        CREATE INDEX IF NOT EXISTS repo_mentions_file ON repo_mentions(file);

        CREATE TABLE IF NOT EXISTS repo_refs (
            from_symbol TEXT NOT NULL,
            to_symbol TEXT NOT NULL,
            ref_kind TEXT NOT NULL,
            file TEXT NOT NULL,
            line INTEGER NOT NULL,
            snippet TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS repo_refs_to_symbol ON repo_refs(to_symbol);
        CREATE INDEX IF NOT EXISTS repo_refs_from_symbol ON repo_refs(from_symbol);
        CREATE INDEX IF NOT EXISTS repo_refs_file ON repo_refs(file);

        CREATE TABLE IF NOT EXISTS narrative_source_status (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS narrative_events (
            event_id TEXT PRIMARY KEY,
            timestamp INTEGER NOT NULL,
            kind TEXT NOT NULL,
            title TEXT NOT NULL,
            text TEXT NOT NULL,
            commit_sha TEXT,
            pull_request INTEGER,
            url TEXT,
            authority TEXT NOT NULL,
            may_guide_discovery INTEGER NOT NULL,
            may_explain_intent INTEGER NOT NULL,
            may_establish_formal_fact INTEGER NOT NULL,
            may_establish_empirical_fact INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS narrative_events_timestamp
            ON narrative_events(timestamp, event_id);
        CREATE INDEX IF NOT EXISTS narrative_events_commit
            ON narrative_events(commit_sha);
        CREATE INDEX IF NOT EXISTS narrative_events_pr
            ON narrative_events(pull_request);

        CREATE TABLE IF NOT EXISTS narrative_event_paths (
            event_id TEXT NOT NULL REFERENCES narrative_events(event_id) ON DELETE CASCADE,
            path TEXT NOT NULL,
            PRIMARY KEY(event_id, path)
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS narrative_event_objects (
            event_id TEXT NOT NULL REFERENCES narrative_events(event_id) ON DELETE CASCADE,
            object_id TEXT NOT NULL,
            role TEXT NOT NULL CHECK(role IN ('touched', 'introduced', 'removed')),
            PRIMARY KEY(event_id, object_id, role)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS narrative_event_objects_object
            ON narrative_event_objects(object_id, role);

        CREATE TABLE IF NOT EXISTS narrative_statements (
            event_id TEXT NOT NULL REFERENCES narrative_events(event_id) ON DELETE CASCADE,
            statement_kind TEXT NOT NULL CHECK(
                statement_kind IN ('claimed_delta', 'frontier', 'nonclaim', 'verification')
            ),
            ordinal INTEGER NOT NULL,
            text TEXT NOT NULL,
            PRIMARY KEY(event_id, statement_kind, ordinal)
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS pull_requests (
            number INTEGER PRIMARY KEY,
            title TEXT NOT NULL,
            body TEXT NOT NULL,
            head_ref TEXT NOT NULL,
            base_ref TEXT NOT NULL,
            created_at INTEGER,
            merged_at INTEGER,
            closed_at INTEGER,
            merge_commit TEXT,
            url TEXT
        );

        CREATE TABLE IF NOT EXISTS pull_request_commits (
            pull_request INTEGER NOT NULL REFERENCES pull_requests(number) ON DELETE CASCADE,
            ordinal INTEGER NOT NULL,
            commit_sha TEXT NOT NULL,
            PRIMARY KEY(pull_request, ordinal)
        ) WITHOUT ROWID;
        """
    )
    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES('repo_inventory_schema', ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (REPO_INVENTORY_SCHEMA,),
    )
    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES('narrative_schema', ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (NARRATIVE_SCHEMA,),
    )
    conn.commit()


def _table_exists(conn: sqlite3.Connection, table: str, *, schema: str = "main") -> bool:
    row = conn.execute(
        f"SELECT 1 FROM {schema}.sqlite_master WHERE type='table' AND name=?",
        (table,),
    ).fetchone()
    return row is not None


def _legacy_json(value: Any, default: Any) -> Any:
    """Decode legacy repo-index payloads at the migration boundary only."""

    if value is None:
        return default
    try:
        return json.loads(str(value))
    except (TypeError, ValueError, json.JSONDecodeError):
        return default


def _legacy_signature(path: Path) -> tuple[int, int]:
    stat = path.stat()
    return stat.st_mtime_ns, stat.st_size


def sync_legacy_repo_index(
    root: Path,
    conn: sqlite3.Connection,
    *,
    legacy_path: Optional[Path] = None,
    force: bool = False,
) -> bool:
    """Import the historical `.repo-index` DB into normalized shared tables.

    This is a compatibility ingress, not a second live authority.  The import is
    skipped when the legacy file has not changed since the previous migration.
    """

    root = root.resolve()
    chosen = legacy_path or LEGACY_REPO_INDEX
    path = chosen if chosen.is_absolute() else root / chosen
    if not path.exists():
        return False
    ensure_repository_schema(conn)
    mtime_ns, size = _legacy_signature(path)
    previous_mtime = conn.execute(
        "SELECT value FROM repository_meta WHERE key='legacy_repo_index_mtime_ns'"
    ).fetchone()
    previous_size = conn.execute(
        "SELECT value FROM repository_meta WHERE key='legacy_repo_index_size'"
    ).fetchone()
    if (
        not force
        and previous_mtime is not None
        and previous_size is not None
        and int(previous_mtime[0]) == mtime_ns
        and int(previous_size[0]) == size
        and conn.execute("SELECT count(*) FROM repo_files").fetchone()[0] > 0
    ):
        return False

    conn.execute("ATTACH DATABASE ? AS legacy_repo_index", (str(path),))
    try:
        if not _table_exists(conn, "files", schema="legacy_repo_index") or not _table_exists(
            conn, "symbols", schema="legacy_repo_index"
        ):
            return False

        conn.execute("DELETE FROM repo_refs")
        conn.execute("DELETE FROM repo_mentions")
        conn.execute("DELETE FROM repo_requirements")
        conn.execute("DELETE FROM repo_symbol_tags")
        conn.execute("DELETE FROM repo_symbols")
        conn.execute("DELETE FROM repo_doc_links")
        conn.execute("DELETE FROM repo_file_imports")
        conn.execute("DELETE FROM repo_files")

        file_rows = conn.execute(
            "SELECT * FROM legacy_repo_index.files ORDER BY path"
        ).fetchall()
        for row in file_rows:
            conn.execute(
                """
                INSERT INTO repo_files(
                    path, language, module, mtime_ns, size, sha256, indexed_at
                ) VALUES(?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    row["path"],
                    row["language"],
                    row["module"],
                    int(row["mtime_ns"]),
                    int(row["size"]),
                    row["sha256"],
                    int(row["indexed_at"]),
                ),
            )
            keys = set(row.keys())
            for imported in _legacy_json(row["imports_json"], []) if "imports_json" in keys else []:
                conn.execute(
                    "INSERT OR IGNORE INTO repo_file_imports(file, imported_module, line, owner_symbol) VALUES(?, ?, 0, NULL)",
                    (row["path"], str(imported)),
                )
            for url in _legacy_json(row["doc_links_json"], []) if "doc_links_json" in keys else []:
                conn.execute(
                    "INSERT OR IGNORE INTO repo_doc_links(file, url) VALUES(?, ?)",
                    (row["path"], str(url)),
                )

        symbol_rows = conn.execute(
            "SELECT * FROM legacy_repo_index.symbols ORDER BY symbol_id"
        ).fetchall()
        for row in symbol_rows:
            status = _legacy_json(row["status_json"], {})
            conn.execute(
                """
                INSERT INTO repo_symbols(
                    symbol_id, name, kind, language, module, file,
                    line_start, line_end, promotion, authority, truth, source
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    row["symbol_id"],
                    row["name"],
                    row["kind"],
                    row["language"],
                    row["module"],
                    row["file"],
                    int(row["line_start"]),
                    int(row["line_end"]),
                    str(status.get("promotion", "unknown")),
                    str(status.get("authority", "unknown")),
                    str(status.get("truth", "unknown")),
                    str(status.get("source", row["language"] or "unknown")),
                ),
            )
            for tag in _legacy_json(row["tags_json"], []):
                conn.execute(
                    "INSERT OR IGNORE INTO repo_symbol_tags(symbol_id, tag) VALUES(?, ?)",
                    (row["symbol_id"], str(tag)),
                )
            requirements = _legacy_json(row["requirements_json"], {})
            if isinstance(requirements, dict):
                for requirement_class, items in requirements.items():
                    if not isinstance(items, list):
                        continue
                    for item in items:
                        if not isinstance(item, dict):
                            continue
                        required_symbol = item.get("symbol") or item.get("required_symbol")
                        if not required_symbol:
                            continue
                        conn.execute(
                            """
                            INSERT OR IGNORE INTO repo_requirements(
                                symbol_id, requirement_class, requirement_kind,
                                required_symbol, source
                            ) VALUES(?, ?, ?, ?, ?)
                            """,
                            (
                                row["symbol_id"],
                                str(requirement_class),
                                str(item.get("kind", "unknown")),
                                str(required_symbol),
                                str(item.get("source", "legacy-repo-index")),
                            ),
                        )

        if _table_exists(conn, "imports", schema="legacy_repo_index"):
            for row in conn.execute("SELECT * FROM legacy_repo_index.imports"):
                conn.execute(
                    "INSERT OR IGNORE INTO repo_file_imports(file, imported_module, line, owner_symbol) VALUES(?, ?, ?, ?)",
                    (
                        row["file"],
                        row["imported_module"],
                        int(row["line"]),
                        row["owner_symbol"],
                    ),
                )
        if _table_exists(conn, "mentions", schema="legacy_repo_index"):
            for row in conn.execute("SELECT * FROM legacy_repo_index.mentions"):
                conn.execute(
                    "INSERT INTO repo_mentions(file, line, owner_symbol, token, snippet, source_kind) VALUES(?, ?, ?, ?, ?, ?)",
                    tuple(row),
                )
        if _table_exists(conn, "refs", schema="legacy_repo_index"):
            for row in conn.execute("SELECT * FROM legacy_repo_index.refs"):
                conn.execute(
                    "INSERT INTO repo_refs(from_symbol, to_symbol, ref_kind, file, line, snippet) VALUES(?, ?, ?, ?, ?, ?)",
                    tuple(row),
                )

        schema_row = conn.execute(
            "SELECT value FROM legacy_repo_index.meta WHERE key='schema_version'"
        ).fetchone() if _table_exists(conn, "meta", schema="legacy_repo_index") else None
        generated_row = conn.execute(
            "SELECT value FROM legacy_repo_index.meta WHERE key='generated_at'"
        ).fetchone() if _table_exists(conn, "meta", schema="legacy_repo_index") else None
        metadata = {
            "legacy_repo_index_path": str(path),
            "legacy_repo_index_mtime_ns": str(mtime_ns),
            "legacy_repo_index_size": str(size),
            "legacy_repo_index_schema": str(schema_row[0]) if schema_row else "unknown",
            "legacy_repo_index_generated_at": str(generated_row[0]) if generated_row else "unknown",
        }
        for key, value in metadata.items():
            conn.execute(
                "INSERT INTO repository_meta(key, value) VALUES(?, ?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, value),
            )
        conn.commit()
        return True
    finally:
        try:
            conn.execute("DETACH DATABASE legacy_repo_index")
        except sqlite3.DatabaseError:
            pass


def _status_text(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if value is None:
        return ""
    return str(value)


def replace_narrative_events(
    conn: sqlite3.Connection,
    *,
    events: Iterable[dict[str, Any]],
    source_status: dict[str, Any],
) -> None:
    ensure_repository_schema(conn)
    conn.execute("DELETE FROM narrative_statements")
    conn.execute("DELETE FROM narrative_event_objects")
    conn.execute("DELETE FROM narrative_event_paths")
    conn.execute("DELETE FROM narrative_events")
    conn.execute("DELETE FROM narrative_source_status")

    for key, value in sorted(source_status.items()):
        conn.execute(
            "INSERT INTO narrative_source_status(key, value) VALUES(?, ?)",
            (str(key), _status_text(value)),
        )

    statement_fields = {
        "claimed_delta": "claimed_delta",
        "frontier": "frontier",
        "nonclaims": "nonclaim",
        "verification": "verification",
    }
    for event in events:
        event_id = str(event["event_id"])
        conn.execute(
            """
            INSERT INTO narrative_events(
                event_id, timestamp, kind, title, text, commit_sha,
                pull_request, url, authority, may_guide_discovery,
                may_explain_intent, may_establish_formal_fact,
                may_establish_empirical_fact
            ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                event_id,
                int(event.get("timestamp", 0) or 0),
                str(event.get("kind", "unknown")),
                str(event.get("title", "")),
                str(event.get("text", "")),
                event.get("commit"),
                event.get("pull_request"),
                event.get("url"),
                str(event.get("authority", "development-narrative")),
                int(bool(event.get("may_guide_discovery", True))),
                int(bool(event.get("may_explain_intent", True))),
                int(bool(event.get("may_establish_formal_fact", False))),
                int(bool(event.get("may_establish_empirical_fact", False))),
            ),
        )
        for path in event.get("touched_paths", ()):
            conn.execute(
                "INSERT OR IGNORE INTO narrative_event_paths(event_id, path) VALUES(?, ?)",
                (event_id, str(path)),
            )
        for field, role in (
            ("touched_objects", "touched"),
            ("introduced_objects", "introduced"),
            ("removed_objects", "removed"),
        ):
            for object_id in event.get(field, ()):
                conn.execute(
                    "INSERT OR IGNORE INTO narrative_event_objects(event_id, object_id, role) VALUES(?, ?, ?)",
                    (event_id, str(object_id), role),
                )
        for field, statement_kind in statement_fields.items():
            for ordinal, text in enumerate(event.get(field, ())):
                conn.execute(
                    "INSERT INTO narrative_statements(event_id, statement_kind, ordinal, text) VALUES(?, ?, ?, ?)",
                    (event_id, statement_kind, ordinal, str(text)),
                )
    conn.commit()


def replace_pull_requests(conn: sqlite3.Connection, pull_requests: Iterable[dict[str, Any]]) -> None:
    ensure_repository_schema(conn)
    conn.execute("DELETE FROM pull_request_commits")
    conn.execute("DELETE FROM pull_requests")
    for item in pull_requests:
        number = int(item["number"])
        conn.execute(
            """
            INSERT INTO pull_requests(
                number, title, body, head_ref, base_ref, created_at,
                merged_at, closed_at, merge_commit, url
            ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                number,
                str(item.get("title", "")),
                str(item.get("body", "")),
                str(item.get("head_ref", item.get("headRefName", ""))),
                str(item.get("base_ref", item.get("baseRefName", ""))),
                item.get("created_at", item.get("createdAt")),
                item.get("merged_at", item.get("mergedAt")),
                item.get("closed_at", item.get("closedAt")),
                item.get("merge_commit", item.get("mergeCommit")),
                item.get("url"),
            ),
        )
        commits = item.get("commits", ())
        for ordinal, commit in enumerate(commits):
            sha = commit.get("oid") if isinstance(commit, dict) else commit
            if sha:
                conn.execute(
                    "INSERT INTO pull_request_commits(pull_request, ordinal, commit_sha) VALUES(?, ?, ?)",
                    (number, ordinal, str(sha)),
                )
    conn.commit()


def _tokens(value: str) -> set[str]:
    return {token.lower() for token in _TOKEN_RE.findall(value) if len(token) > 1}


def _narrative_score(query: str, event: dict[str, Any]) -> float:
    q = query.strip().lower()
    query_tokens = _tokens(q)
    title = str(event.get("title", ""))
    text = str(event.get("text", ""))
    objects = " ".join(event.get("touched_objects", ()))
    haystack = "\n".join((title, text, objects))
    tokens = _tokens(haystack)
    token_score = len(query_tokens & tokens) / len(query_tokens) if query_tokens else 0.0
    object_tokens = _tokens(objects)
    object_score = len(query_tokens & object_tokens) / len(query_tokens) if query_tokens else 0.0
    name_score = SequenceMatcher(None, q, title.lower()).ratio() if q else 0.0
    exact = 1.0 if q and q in haystack.lower() else 0.0
    return min(1.0, 0.45 * token_score + 0.25 * object_score + 0.20 * name_score + 0.10 * exact)


def narrative_coverage(conn: sqlite3.Connection) -> dict[str, Any]:
    ensure_repository_schema(conn)
    rows = conn.execute("SELECT key, value FROM narrative_source_status").fetchall()
    if not rows:
        return {
            "available": False,
            "complete": False,
            "authority": "development-narrative",
            "source_status": {},
        }
    status = {str(row[0]): str(row[1]) for row in rows}
    complete = status.get("commit_history_complete", "").lower() in {"1", "true", "yes"}
    return {
        "available": True,
        "complete": complete,
        "authority": "development-narrative",
        "source_status": status,
    }


def load_narrative_events(conn: sqlite3.Connection) -> list[dict[str, Any]]:
    ensure_repository_schema(conn)
    events: list[dict[str, Any]] = []
    for row in conn.execute("SELECT * FROM narrative_events ORDER BY timestamp, event_id"):
        event_id = row["event_id"] if isinstance(row, sqlite3.Row) else row[0]
        keys = row.keys() if isinstance(row, sqlite3.Row) else ()
        def field(name: str, index: int):
            return row[name] if name in keys else row[index]
        event = {
            "event_id": str(event_id),
            "timestamp": int(field("timestamp", 1)),
            "kind": str(field("kind", 2)),
            "title": str(field("title", 3)),
            "text": str(field("text", 4)),
            "commit": field("commit_sha", 5),
            "pull_request": field("pull_request", 6),
            "url": field("url", 7),
            "authority": str(field("authority", 8)),
            "may_guide_discovery": bool(field("may_guide_discovery", 9)),
            "may_explain_intent": bool(field("may_explain_intent", 10)),
            "may_establish_formal_fact": bool(field("may_establish_formal_fact", 11)),
            "may_establish_empirical_fact": bool(field("may_establish_empirical_fact", 12)),
            "touched_paths": [],
            "touched_objects": [],
            "introduced_objects": [],
            "removed_objects": [],
            "claimed_delta": [],
            "frontier": [],
            "nonclaims": [],
            "verification": [],
        }
        for item in conn.execute(
            "SELECT path FROM narrative_event_paths WHERE event_id=? ORDER BY path",
            (event_id,),
        ):
            event["touched_paths"].append(str(item[0]))
        for item in conn.execute(
            "SELECT object_id, role FROM narrative_event_objects WHERE event_id=? ORDER BY role, object_id",
            (event_id,),
        ):
            role = str(item[1])
            target = {
                "touched": "touched_objects",
                "introduced": "introduced_objects",
                "removed": "removed_objects",
            }[role]
            event[target].append(str(item[0]))
        for item in conn.execute(
            "SELECT statement_kind, text FROM narrative_statements WHERE event_id=? ORDER BY statement_kind, ordinal",
            (event_id,),
        ):
            target = {
                "claimed_delta": "claimed_delta",
                "frontier": "frontier",
                "nonclaim": "nonclaims",
                "verification": "verification",
            }[str(item[0])]
            event[target].append(str(item[1]))
        events.append(event)
    return events


def search_narrative(
    conn: sqlite3.Connection,
    query: str,
    *,
    limit: int = 40,
    threshold: float = 0.18,
) -> dict[str, Any]:
    coverage = narrative_coverage(conn)
    if not coverage["available"]:
        return {**coverage, "matches": []}
    ranked: list[dict[str, Any]] = []
    for event in load_narrative_events(conn):
        score = _narrative_score(query, event)
        if score < threshold:
            continue
        item = dict(event)
        item["archaeology_score"] = score
        ranked.append(item)
    ranked.sort(
        key=lambda item: (
            -float(item["archaeology_score"]),
            -int(item["timestamp"]),
            item["event_id"],
        )
    )
    return {
        **coverage,
        "may_establish_formal_fact": False,
        "may_establish_empirical_fact": False,
        "matches": ranked[:limit],
    }
