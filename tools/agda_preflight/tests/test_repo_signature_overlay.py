import json
import sqlite3
from pathlib import Path

from agda_preflight.source_index import SourceIndex
from agda_preflight.repo_index_bridge import RepoIndexReader
from agda_preflight.repo_signature_overlay import sync_repo_signatures


def _seed(root: Path) -> Path:
    source = root / "DASHI" / "Core" / "Foo.agda"
    source.parent.mkdir(parents=True)
    source.write_text(
        "module DASHI.Core.Foo where\n\nfoo : (x : Nat) → Nat\nfoo x = x\n\nbar : (y : Nat) → Nat\nbar y = y\n",
        encoding="utf-8",
    )
    stat = source.stat()
    repo = root / ".repo-index" / "index.sqlite3"
    repo.parent.mkdir(parents=True)
    conn = sqlite3.connect(repo)
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
    conn.execute("INSERT INTO meta VALUES('generated_at','123')")
    conn.execute(
        "INSERT INTO files VALUES(?, 'agda', ?, ?, ?, '', 123, '[]', '[]', '[]')",
        ("DASHI/Core/Foo.agda", "DASHI.Core.Foo", stat.st_mtime_ns, stat.st_size),
    )
    status = json.dumps({"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"})
    for name, start, end in (("foo", 3, 3), ("bar", 6, 6)):
        conn.execute(
            "INSERT INTO symbols VALUES(?, ?, 'function', 'agda', ?, ?, ?, ?, ?, '[]', '{}')",
            ("DASHI.Core.Foo." + name, name, "DASHI.Core.Foo", "DASHI/Core/Foo.agda", start, end, status),
        )
    conn.commit()
    conn.close()
    return repo


def test_repo_signature_overlay_makes_repo_wide_signature_equivalence_searchable(tmp_path: Path):
    repo_path = _seed(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as source_index:
        with RepoIndexReader(tmp_path, repo_path) as repo:
            result = sync_repo_signatures(tmp_path, repo, source_index.connection)
        assert result["symbols_with_signatures"] == 2
        related = source_index.related_symbols("DASHI.Core.Foo.foo")
    assert any(item["name"] == "bar" for item in related["signature_equivalent"])
