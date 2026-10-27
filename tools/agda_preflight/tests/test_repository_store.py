import json
import sqlite3
from pathlib import Path

from agda_preflight.repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    narrative_coverage,
    replace_narrative_events,
    search_narrative,
    sync_legacy_repo_index,
)


def test_unified_repository_database_path_is_single_product_path():
    assert DEFAULT_REPOSITORY_DB == Path(".dashi/repository.sqlite3")


def test_narrative_events_are_normalized_relational_rows(tmp_path: Path):
    database = tmp_path / DEFAULT_REPOSITORY_DB
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)

    replace_narrative_events(
        conn,
        events=[
            {
                "event_id": "commit:abc",
                "timestamp": 7,
                "kind": "commit",
                "title": "Recover spatial C3",
                "text": "Recovered literal spatial C3 action. Remaining leaf: A1 covariance.",
                "commit": "abc",
                "pull_request": None,
                "url": None,
                "touched_paths": ["DASHI/Physics/C3.agda"],
                "touched_objects": ["DASHI.Physics.C3::spatialC3"],
                "introduced_objects": ["DASHI.Physics.C3::spatialC3"],
                "removed_objects": [],
                "authority": "development-narrative",
                "may_guide_discovery": True,
                "may_explain_intent": True,
                "may_establish_formal_fact": False,
                "may_establish_empirical_fact": False,
                "claimed_delta": ["Recovered literal spatial C3 action."],
                "frontier": ["Remaining leaf: A1 covariance."],
                "nonclaims": [],
                "verification": [],
            }
        ],
        source_status={
            "git_commits": 1,
            "commit_history_complete": True,
            "semantic_history_linked": True,
        },
    )

    result = search_narrative(conn, "spatial C3")
    assert result["available"] is True
    assert result["complete"] is True
    assert result["matches"][0]["event_id"] == "commit:abc"
    assert result["matches"][0]["touched_objects"] == ["DASHI.Physics.C3::spatialC3"]
    assert result["matches"][0]["frontier"] == ["Remaining leaf: A1 covariance."]

    for table in (
        "narrative_events",
        "narrative_event_paths",
        "narrative_event_objects",
        "narrative_statements",
        "narrative_source_status",
    ):
        columns = [row[1] for row in conn.execute(f"PRAGMA table_info({table})")]
        assert not any("json" in column.lower() for column in columns)
    conn.close()


def _legacy_repo_index(root: Path) -> Path:
    path = root / ".repo-index" / "index.sqlite3"
    path.parent.mkdir(parents=True)
    conn = sqlite3.connect(path)
    conn.executescript(
        """
        CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE files(path TEXT PRIMARY KEY, language TEXT NOT NULL, module TEXT,
          mtime_ns INTEGER NOT NULL, size INTEGER NOT NULL, sha256 TEXT NOT NULL,
          indexed_at INTEGER NOT NULL, imports_json TEXT NOT NULL,
          doc_links_json TEXT NOT NULL, symbols_json TEXT NOT NULL);
        CREATE TABLE symbols(symbol_id TEXT PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
          language TEXT NOT NULL, module TEXT, file TEXT NOT NULL,
          line_start INTEGER NOT NULL, line_end INTEGER NOT NULL,
          status_json TEXT NOT NULL, tags_json TEXT NOT NULL, requirements_json TEXT NOT NULL);
        CREATE TABLE refs(from_symbol TEXT NOT NULL, to_symbol TEXT NOT NULL,
          ref_kind TEXT NOT NULL, file TEXT NOT NULL, line INTEGER NOT NULL, snippet TEXT NOT NULL);
        """
    )
    conn.execute("INSERT INTO meta VALUES('schema_version','2.0.0')")
    conn.execute("INSERT INTO meta VALUES('generated_at','7')")
    conn.execute(
        "INSERT INTO files VALUES(?, 'agda', ?, 1, 2, 'sha', 7, '[]', '[]', '[]')",
        ("DASHI/Core/Foo.agda", "DASHI.Core.Foo"),
    )
    conn.execute(
        "INSERT INTO symbols VALUES(?, ?, 'function', 'agda', ?, ?, 3, 3, ?, ?, ?)",
        (
            "DASHI.Core.Foo.knownThing",
            "knownThing",
            "DASHI.Core.Foo",
            "DASHI/Core/Foo.agda",
            json.dumps({"promotion": "promoted", "authority": "unknown", "truth": "unknown", "source": "agda"}),
            json.dumps(["Core"]),
            json.dumps({"syntactic_requirements": [{"kind": "field", "symbol": "witness", "source": "fixture"}]}),
        ),
    )
    conn.commit()
    conn.close()
    return path


def test_legacy_repo_index_migrates_into_normalized_repo_tables(tmp_path: Path):
    legacy = _legacy_repo_index(tmp_path)
    database = tmp_path / DEFAULT_REPOSITORY_DB
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)

    migrated = sync_legacy_repo_index(tmp_path, conn, legacy_path=legacy)
    assert migrated is True

    symbol = conn.execute(
        "SELECT * FROM repo_symbols WHERE symbol_id = 'DASHI.Core.Foo.knownThing'"
    ).fetchone()
    assert symbol["promotion"] == "promoted"
    assert symbol["source"] == "agda"
    assert conn.execute(
        "SELECT tag FROM repo_symbol_tags WHERE symbol_id = ?",
        (symbol["symbol_id"],),
    ).fetchone()[0] == "Core"
    requirement = conn.execute(
        "SELECT requirement_kind, required_symbol, source FROM repo_requirements WHERE symbol_id = ?",
        (symbol["symbol_id"],),
    ).fetchone()
    assert tuple(requirement) == ("field", "witness", "fixture")
    assert narrative_coverage(conn)["available"] is False
    conn.close()
