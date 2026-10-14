import json
import sqlite3
from pathlib import Path

from agda_preflight.repo_index_bridge import RepoIndexReader


def _seed_repo_index(root: Path) -> Path:
    source = root / "DASHI" / "Core" / "Foo.agda"
    source.parent.mkdir(parents=True)
    source.write_text("module DASHI.Core.Foo where\n\ntarget : Nat\ntarget = 0\n", encoding="utf-8")
    stat = source.stat()
    index_path = root / ".repo-index" / "index.sqlite3"
    index_path.parent.mkdir(parents=True)
    conn = sqlite3.connect(index_path)
    conn.executescript(
        """
        CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE files(
          path TEXT PRIMARY KEY, language TEXT NOT NULL, module TEXT,
          mtime_ns INTEGER NOT NULL, size INTEGER NOT NULL, sha256 TEXT NOT NULL,
          indexed_at INTEGER NOT NULL, imports_json TEXT NOT NULL,
          doc_links_json TEXT NOT NULL, symbols_json TEXT NOT NULL
        );
        CREATE TABLE symbols(
          symbol_id TEXT PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
          language TEXT NOT NULL, module TEXT, file TEXT NOT NULL,
          line_start INTEGER NOT NULL, line_end INTEGER NOT NULL,
          status_json TEXT NOT NULL, tags_json TEXT NOT NULL,
          requirements_json TEXT NOT NULL
        );
        CREATE TABLE refs(
          from_symbol TEXT NOT NULL, to_symbol TEXT NOT NULL,
          ref_kind TEXT NOT NULL, file TEXT NOT NULL, line INTEGER NOT NULL,
          snippet TEXT NOT NULL
        );
        """
    )
    conn.execute("INSERT INTO meta VALUES('schema_version', '2.0.0')")
    conn.execute(
        "INSERT INTO files VALUES(?, 'agda', ?, ?, ?, '', 0, '[]', '[]', ?)",
        ("DASHI/Core/Foo.agda", "DASHI.Core.Foo", stat.st_mtime_ns, stat.st_size, json.dumps(["DASHI.Core.Foo", "DASHI.Core.Foo.target"])),
    )
    unknown = json.dumps({"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"})
    conn.execute(
        "INSERT INTO symbols VALUES(?, ?, 'module', 'agda', ?, ?, 1, 1, ?, '[\"module\"]', '{}')",
        ("DASHI.Core.Foo", "Foo", "DASHI.Core.Foo", "DASHI/Core/Foo.agda", unknown),
    )
    conn.execute(
        "INSERT INTO symbols VALUES(?, ?, 'function', 'agda', ?, ?, 3, 4, ?, '[]', '{}')",
        ("DASHI.Core.Foo.target", "target", "DASHI.Core.Foo", "DASHI/Core/Foo.agda", unknown),
    )
    conn.commit()
    conn.close()
    return index_path


def test_repo_index_reader_returns_symbol_spans_and_status(tmp_path: Path):
    index_path = _seed_repo_index(tmp_path)
    with RepoIndexReader(tmp_path, index_path) as reader:
        matches = reader.search_symbols("target")
    assert matches[0]["symbol_id"] == "DASHI.Core.Foo.target"
    assert matches[0]["line_start"] == 3
    assert matches[0]["surface_role"] == "canonical"


def test_repo_index_reader_completion_requires_fresh_whole_surface(tmp_path: Path):
    index_path = _seed_repo_index(tmp_path)
    with RepoIndexReader(tmp_path, index_path) as reader:
        status = reader.coverage_status()
    assert status["complete"] is True
    hidden = tmp_path / "DASHI" / "Hidden.agda"
    hidden.write_text("module DASHI.Hidden where\n", encoding="utf-8")
    with RepoIndexReader(tmp_path, index_path) as reader:
        status = reader.coverage_status()
    assert status["complete"] is False
    assert status["state"] == "stale-or-incomplete"


def test_repo_index_reader_exposes_refs_and_requirements(tmp_path: Path):
    index_path = _seed_repo_index(tmp_path)
    conn = sqlite3.connect(index_path)
    conn.execute(
        "INSERT INTO refs VALUES('DASHI.Core.Foo', 'DASHI.Core.Foo.target', 'definition-use', 'DASHI/Core/Foo.agda', 4, 'target = 0')"
    )
    conn.commit()
    conn.close()
    with RepoIndexReader(tmp_path, index_path) as reader:
        detail = reader.object_detail("DASHI.Core.Foo.target")
    assert detail["refs"][0]["ref_kind"] == "definition-use"
    assert "requirements" in detail["symbol"]
