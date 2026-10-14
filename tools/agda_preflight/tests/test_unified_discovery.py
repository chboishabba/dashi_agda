import json
import sqlite3
from pathlib import Path

from agda_preflight.source_index import SourceIndex
from agda_preflight.repo_index_bridge import RepoIndexReader
from agda_preflight.unified_discovery import UnifiedDiscovery


def _seed_repo_index(root: Path) -> Path:
    sources = {
        "DASHI/Core/Foo.agda": "module DASHI.Core.Foo where\n\ntarget : Nat\ntarget = 0\n",
        "DASHI/Physics/Closure/FooRound1Exact.agda": "module DASHI.Physics.Closure.FooRound1Exact where\n\ntarget : Nat\ntarget = 0\n",
        "DASHI/Physics/Closure/FooRound2Exact.agda": "module DASHI.Physics.Closure.FooRound2Exact where\n\ntarget : Nat\ntarget = 0\nnewThing : Nat\nnewThing = 1\n",
    }
    for rel, text in sources.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    index_path = root / ".repo-index" / "index.sqlite3"
    index_path.parent.mkdir(parents=True)
    conn = sqlite3.connect(index_path)
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
    conn.execute("INSERT INTO meta VALUES('schema_version', '2.0.0')")
    unknown = json.dumps({"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"})
    for rel in sources:
        path = root / rel
        module = rel[:-5].replace("/", ".")
        stat = path.stat()
        names = ["target"] + (["newThing"] if "Round2" in module else [])
        ids = [module] + [module + "." + name for name in names]
        conn.execute(
            "INSERT INTO files VALUES(?, 'agda', ?, ?, ?, '', 0, '[]', '[]', ?)",
            (rel, module, stat.st_mtime_ns, stat.st_size, json.dumps(ids)),
        )
        conn.execute(
            "INSERT INTO symbols VALUES(?, ?, 'module', 'agda', ?, ?, 1, 1, ?, '[\"module\"]', '{}')",
            (module, module.rsplit('.', 1)[-1], module, rel, unknown),
        )
        for i, name in enumerate(names):
            conn.execute(
                "INSERT INTO symbols VALUES(?, ?, 'function', 'agda', ?, ?, ?, ?, ?, '[]', '{}')",
                (module + "." + name, name, module, rel, 3 + i * 2, 4 + i * 2, unknown),
            )
    conn.commit()
    conn.close()
    return index_path


def _seed_preflight(index: SourceIndex) -> None:
    interface = {
        "module_name": "DASHI.Core.Foo",
        "imports": [],
        "signatures": [
            {"name": "target", "type_text": "Nat", "terminal_head": "Nat", "explicit_arity": 0},
            {"name": "sameShape", "type_text": "Nat", "terminal_head": "Nat", "explicit_arity": 0},
        ],
        "records": [], "data_constructors": [], "nested_modules": [],
        "module_parameter_count": 0, "public_reexports": [], "resolved_exports": ["target", "sameShape"],
    }
    index.connection.execute(
        """INSERT OR REPLACE INTO modules(path,module_name,mtime_ns,size,source_sha256,
        api_base_sha256,api_fingerprint,public_imports_json,interface_json,dependency_fingerprint,
        diagnostics_json,top_diagnostic_json,top_fixable_diagnostic_json,updated_ns)
        VALUES('DASHI/Core/Foo.agda','DASHI.Core.Foo',0,0,'','','','[]',?,'','[]','','',1)""",
        (json.dumps(interface),),
    )
    index.connection.commit()
    index.refresh_semantic_catalog()


def test_unified_search_uses_repo_index_as_inventory_and_hides_rounds(tmp_path: Path):
    repo_path = _seed_repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        _seed_preflight(source_index)
        with RepoIndexReader(tmp_path, repo_path) as repo:
            discovery = UnifiedDiscovery(tmp_path, source_index, repo)
            live = discovery.search_symbols("target")
            history = discovery.search_symbols("target", include_history=True)
    assert [item["qualified_name"] for item in live] == ["DASHI.Core.Foo.target"]
    assert len(history) == 3
    assert all("line_start" in item for item in history)


def test_unified_related_uses_preflight_signature_overlay(tmp_path: Path):
    repo_path = _seed_repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        _seed_preflight(source_index)
        with RepoIndexReader(tmp_path, repo_path) as repo:
            discovery = UnifiedDiscovery(tmp_path, source_index, repo)
            report = discovery.related_symbols("DASHI.Core.Foo.target")
    assert report["query_symbol"]["qualified_name"] == "DASHI.Core.Foo.target"
    assert any(item["name"] == "sameShape" for item in report["signature_equivalent"])


def test_unified_absence_requires_fresh_complete_repo_index(tmp_path: Path):
    repo_path = _seed_repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        with RepoIndexReader(tmp_path, repo_path) as repo:
            discovery = UnifiedDiscovery(tmp_path, source_index, repo)
            missing = discovery.discovery_receipt("definitelyMissingXYZ")
    assert missing["absence_claim_permitted"] is True
    extra = tmp_path / "DASHI" / "Unindexed.agda"
    extra.write_text("module DASHI.Unindexed where\n", encoding="utf-8")
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        with RepoIndexReader(tmp_path, repo_path) as repo:
            discovery = UnifiedDiscovery(tmp_path, source_index, repo)
            incomplete = discovery.discovery_receipt("definitelyMissingXYZ")
    assert incomplete["absence_claim_permitted"] is False
    assert incomplete["absence_status"] == "search_incomplete"


def test_unified_round_lineage_uses_repo_wide_inventory(tmp_path: Path):
    repo_path = _seed_repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        with RepoIndexReader(tmp_path, repo_path) as repo:
            discovery = UnifiedDiscovery(tmp_path, source_index, repo)
            report = discovery.round_lineage("DASHI.Physics.Closure.Foo")
    family = report["families"][0]
    assert family["rounds"] == [1, 2]
    assert family["transitions"][0]["added"] == 1
