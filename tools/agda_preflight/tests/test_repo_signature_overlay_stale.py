import json
import sqlite3
from pathlib import Path

from agda_preflight.repo_index_bridge import RepoIndexReader
from agda_preflight.repo_signature_overlay import sync_repo_signatures
from agda_preflight.source_index import SourceIndex


def test_stale_repo_index_does_not_rebuild_signature_overlay(tmp_path: Path):
    source = tmp_path / "DASHI" / "Foo.agda"
    source.parent.mkdir(parents=True)
    source.write_text("module DASHI.Foo where\n\nfoo : Nat\nfoo = 0\n", encoding="utf-8")
    stat = source.stat()
    repo = tmp_path / ".repo-index" / "index.sqlite3"
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
    conn.execute("INSERT INTO meta VALUES('generated_at','1')")
    conn.execute(
        "INSERT INTO files VALUES('DASHI/Foo.agda','agda','DASHI.Foo',?,?, '',1,'[]','[]','[]')",
        (stat.st_mtime_ns - 1, stat.st_size),
    )
    status = json.dumps({"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"})
    conn.execute(
        "INSERT INTO symbols VALUES('DASHI.Foo.foo','foo','function','agda','DASHI.Foo','DASHI/Foo.agda',3,3,?,'[]','{}')",
        (status,),
    )
    conn.commit()
    conn.close()

    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as index:
        with RepoIndexReader(tmp_path, repo) as reader:
            result = sync_repo_signatures(tmp_path, reader, index.connection)
        count = index.connection.execute(
            "SELECT count(*) FROM semantic_symbols WHERE kind='repo-signature'"
        ).fetchone()[0]
    assert result["state"] == "repo-index-stale-or-incomplete"
    assert count == 0
