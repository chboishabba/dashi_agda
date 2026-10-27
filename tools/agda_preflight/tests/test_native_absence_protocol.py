import sqlite3
from pathlib import Path

from agda_preflight.repository_inventory import refresh_repository_inventory
from agda_preflight.repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    replace_narrative_events,
)
from agda_preflight.source_index import SourceIndex


def _write(root: Path, module: str, body: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n\n{body}", encoding="utf-8")
    return path


def test_native_complete_inventory_and_history_authorize_indexed_absence(tmp_path: Path):
    _write(tmp_path, "DASHI.Core.Foo", "knownThing : Nat\nknownThing = 0\n")
    database = tmp_path / DEFAULT_REPOSITORY_DB
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    result = refresh_repository_inventory(tmp_path, conn)
    assert result["parse_errors"] == 0
    replace_narrative_events(
        conn,
        events=[],
        source_status={
            "git_commits": 1,
            "commit_history_complete": True,
            "semantic_history_linked": True,
        },
    )
    conn.close()

    with SourceIndex(tmp_path, database) as index:
        receipt = index.discovery_receipt("certainlyMissingXYZ")
    assert receipt["coverage"]["repository_db"]["producer"] == "agda-preflight"
    assert receipt["coverage"]["repository_db"]["complete"] is True
    assert receipt["coverage"]["narrative_archaeology_complete"] is True
    assert receipt["absence_status"] == "confirmed_no_indexed_candidate"
    assert receipt["absence_claim_permitted"] is True


def test_native_absence_fails_closed_when_source_changes_after_index(tmp_path: Path):
    path = _write(tmp_path, "DASHI.Core.Foo", "knownThing : Nat\nknownThing = 0\n")
    database = tmp_path / DEFAULT_REPOSITORY_DB
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    refresh_repository_inventory(tmp_path, conn)
    replace_narrative_events(
        conn,
        events=[],
        source_status={
            "git_commits": 1,
            "commit_history_complete": True,
            "semantic_history_linked": True,
        },
    )
    conn.close()

    path.write_text(
        "module DASHI.Core.Foo where\n\nknownThing : Nat\nknownThing = 1\nnewThing : Nat\nnewThing = 2\n",
        encoding="utf-8",
    )
    with SourceIndex(tmp_path, database) as index:
        receipt = index.discovery_receipt("certainlyMissingXYZ")
    assert receipt["coverage"]["repository_db"]["complete"] is False
    assert receipt["absence_status"] == "search_incomplete"
    assert receipt["absence_claim_permitted"] is False
