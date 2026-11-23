import sqlite3
from pathlib import Path

from agda_preflight.repository_coverage import repository_inventory_coverage
from agda_preflight.repository_discovery import RepositoryDiscovery
from agda_preflight.repository_inventory import refresh_repository_inventory
from agda_preflight.repository_store import ensure_repository_schema
from agda_preflight.repo_index_bridge import RepoIndexReader


class _Index:
    def __init__(self, connection):
        self.connection = connection


def _write(root: Path, module: str, body: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n\n{body}", encoding="utf-8")
    return path


def test_native_inventory_uses_preflight_parser_and_normalized_signatures(tmp_path: Path):
    _write(
        tmp_path,
        "DASHI.Core.A",
        "foo : (x : Nat) → Nat\nfoo x = x\n\nbar : (y : Nat) → Nat\nbar y = y\n",
    )
    _write(
        tmp_path,
        "DASHI.Core.B",
        "import DASHI.Core.A\n\nbaz : Nat → Nat\nbaz x = x\n",
    )
    database = tmp_path / ".dashi" / "repository.sqlite3"
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)

    result = refresh_repository_inventory(tmp_path, conn)
    assert result["parse_errors"] == 0
    assert result["files"] == 2
    assert conn.execute(
        "SELECT count(*) FROM repo_symbols WHERE kind='signature'"
    ).fetchone()[0] == 3
    assert conn.execute(
        "SELECT count(*) FROM repo_symbol_signatures WHERE signature != ''"
    ).fetchone()[0] >= 3
    assert conn.execute(
        "SELECT imported_module FROM repo_file_imports WHERE file='DASHI/Core/B.agda'"
    ).fetchone()[0] == "DASHI.Core.A"

    coverage = repository_inventory_coverage(tmp_path, conn)
    assert coverage["complete"] is True
    assert coverage["producer"] == "agda-preflight"

    reader = RepoIndexReader(tmp_path, connection=conn)
    discovery = RepositoryDiscovery(tmp_path, _Index(conn), reader)
    related = discovery.related_symbols("DASHI.Core.A.foo", include_history=True)
    assert any(item["name"] == "bar" for item in related["signature_equivalent"])
    assert discovery.search_symbols("foo")[0]["surface_role"] == "canonical"
    conn.close()


def test_native_inventory_coverage_fails_closed_after_source_edit(tmp_path: Path):
    path = _write(tmp_path, "DASHI.Core.A", "foo : Nat\nfoo = 0\n")
    database = tmp_path / ".dashi" / "repository.sqlite3"
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    refresh_repository_inventory(tmp_path, conn)
    assert repository_inventory_coverage(tmp_path, conn)["complete"] is True

    path.write_text(
        "module DASHI.Core.A where\n\nfoo : Nat\nfoo = 1\nbar : Nat\nbar = 2\n",
        encoding="utf-8",
    )
    coverage = repository_inventory_coverage(tmp_path, conn)
    assert coverage["complete"] is False
    assert "DASHI/Core/A.agda" in coverage["stale"]
    conn.close()


def test_native_inventory_staged_batches_resume_after_interruption(tmp_path: Path):
    for idx in range(5):
        _write(
            tmp_path,
            f"DASHI.Core.M{idx}",
            f"sym{idx} : Nat\nsym{idx} = {idx}\n",
        )
    database = tmp_path / ".dashi" / "repository.sqlite3"
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)

    # First complete generation (generation 1)
    first = refresh_repository_inventory(tmp_path, conn, batch_size=2)
    assert first["generation"] == 1
    assert first["files"] == 5
    assert first["batches"] == 3
    assert repository_inventory_coverage(tmp_path, conn)["complete"] is True

    # Simulate an interrupted generation 2 after batch 1 (2 files committed, fail on file 3)
    seen = []

    def interrupt_on_third(position: int, total: int, relative: str) -> None:
        seen.append((position, relative))
        if position == 3:
            raise RuntimeError("simulated interruption after batch 1")

    try:
        refresh_repository_inventory(
            tmp_path,
            conn,
            batch_size=2,
            progress=interrupt_on_third,
        )
    except RuntimeError:
        pass

    # Batch 1 (files 1..2) is durably committed in generation 2, but generation 2 is in-progress
    mid_coverage = repository_inventory_coverage(tmp_path, conn)
    assert mid_coverage["complete"] is False
    assert mid_coverage["generation"] == 1
    assert mid_coverage["target_generation"] == 2
    assert mid_coverage["generation_state"] == "in-progress"
    assert mid_coverage["cursor"] == "DASHI/Core/M1.agda"

    # Resuming completes generation 2, skipping the 2 already-committed files
    resumed = refresh_repository_inventory(tmp_path, conn, batch_size=2)
    assert resumed["generation"] == 2
    assert resumed["resumed_files"] == 2
    assert resumed["indexed_files"] == 3
    assert resumed["files"] == 5
    final_coverage = repository_inventory_coverage(tmp_path, conn)
    assert final_coverage["complete"] is True
    assert final_coverage["generation"] == 2
    assert final_coverage["generation_state"] == "complete"
    assert final_coverage["cursor"] is None
    conn.close()

