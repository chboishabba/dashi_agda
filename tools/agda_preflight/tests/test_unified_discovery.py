import sqlite3
from pathlib import Path

from agda_preflight.repo_index_bridge import RepoIndexReader
from agda_preflight.repository_inventory import refresh_repository_inventory
from agda_preflight.repository_store import ensure_repository_schema
from agda_preflight.source_index import SourceIndex
from agda_preflight.unified_discovery import UnifiedDiscovery


def _write(root: Path, module: str, body: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n\n{body}", encoding="utf-8")
    return path


def _seed_sources(root: Path) -> None:
    _write(
        root,
        "DASHI.Core.Foo",
        "target : Nat\ntarget = 0\n\nsameShape : Nat\nsameShape = 1\n",
    )
    _write(
        root,
        "DASHI.Physics.Closure.FooRound1Exact",
        "target : Nat\ntarget = 0\n",
    )
    _write(
        root,
        "DASHI.Physics.Closure.FooRound2Exact",
        "target : Nat\ntarget = 0\n\nnewThing : Nat\nnewThing = 1\n",
    )


def _build_native(root: Path, database: Path) -> None:
    database.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    result = refresh_repository_inventory(root, conn)
    assert result["parse_errors"] == 0
    conn.close()


def test_unified_search_is_compatibility_name_for_native_inventory_and_hides_rounds(tmp_path: Path):
    _seed_sources(tmp_path)
    database = tmp_path / ".dashi" / "repository.sqlite3"
    _build_native(tmp_path, database)
    with SourceIndex(tmp_path, database) as source_index:
        repo = RepoIndexReader(tmp_path, connection=source_index.connection)
        discovery = UnifiedDiscovery(tmp_path, source_index, repo)
        live = discovery.search_symbols("target")
        history = discovery.search_symbols("target", include_history=True)
    assert [item["qualified_name"] for item in live] == ["DASHI.Core.Foo.target"]
    assert len(history) == 3
    assert all("line_start" in item for item in history)


def test_unified_related_uses_native_signature_rows(tmp_path: Path):
    _seed_sources(tmp_path)
    database = tmp_path / ".dashi" / "repository.sqlite3"
    _build_native(tmp_path, database)
    with SourceIndex(tmp_path, database) as source_index:
        repo = RepoIndexReader(tmp_path, connection=source_index.connection)
        discovery = UnifiedDiscovery(tmp_path, source_index, repo)
        report = discovery.related_symbols("DASHI.Core.Foo.target")
    assert report["query_symbol"]["qualified_name"] == "DASHI.Core.Foo.target"
    assert any(item["name"] == "sameShape" for item in report["signature_equivalent"])


def test_unified_round_lineage_uses_native_repo_wide_inventory(tmp_path: Path):
    _seed_sources(tmp_path)
    database = tmp_path / ".dashi" / "repository.sqlite3"
    _build_native(tmp_path, database)
    with SourceIndex(tmp_path, database) as source_index:
        repo = RepoIndexReader(tmp_path, connection=source_index.connection)
        discovery = UnifiedDiscovery(tmp_path, source_index, repo)
        report = discovery.round_lineage("DASHI.Physics.Closure.Foo")
    family = report["families"][0]
    assert family["rounds"] == [1, 2]
    assert family["transitions"][0]["added"] == 1
