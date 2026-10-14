import json
import sqlite3
from pathlib import Path

from agda_preflight.source_index import SourceIndex


def test_object_detail_returns_repo_index_status_requirements_and_refs(tmp_path: Path):
    source = tmp_path / "DASHI" / "Core" / "Foo.agda"
    source.parent.mkdir(parents=True)
    source.write_text("module DASHI.Core.Foo where\n\nfoo : Nat\nfoo = 0\n", encoding="utf-8")
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
        "INSERT INTO files VALUES('DASHI/Core/Foo.agda','agda','DASHI.Core.Foo',?,?, '',1,'[]','[]','[]')",
        (stat.st_mtime_ns, stat.st_size),
    )
    status = json.dumps({"promotion": "candidate", "authority": "unknown", "truth": "unknown", "source": "agda"})
    reqs = json.dumps({"syntactic_requirements": [{"kind": "name", "symbol": "Nat", "source": "parsed-name"}], "semantic_requirements": []})
    conn.execute(
        "INSERT INTO symbols VALUES('DASHI.Core.Foo.foo','foo','function','agda','DASHI.Core.Foo','DASHI/Core/Foo.agda',3,3,?,'[]',?)",
        (status, reqs),
    )
    conn.execute(
        "INSERT INTO refs VALUES('DASHI.Core.Foo.foo','Nat','definition-use','DASHI/Core/Foo.agda',3,'foo : Nat')"
    )
    conn.commit()
    conn.close()

    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as index:
        detail = index.object_detail("DASHI.Core.Foo.foo")

    assert detail["symbol"]["status"]["promotion"] == "candidate"
    assert detail["symbol"]["requirements"]["syntactic_requirements"][0]["symbol"] == "Nat"
    assert detail["refs"][0]["to_symbol"] == "Nat"
