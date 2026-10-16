import json
import sqlite3
from pathlib import Path

from agda_preflight.repository_store import replace_narrative_events
from agda_preflight.source_index import SourceIndex


def _repo_index(root: Path, *, include_round: bool = False) -> None:
    files = {
        "DASHI/Core/Foo.agda": "module DASHI.Core.Foo where\n\nknownThing : Nat\nknownThing = 0\n",
    }
    if include_round:
        files["DASHI/Physics/Closure/FooRound9Exact.agda"] = (
            "module DASHI.Physics.Closure.FooRound9Exact where\n\noldThing : Nat\noldThing = 0\n"
        )
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
    conn.execute("INSERT INTO meta VALUES('generated_at','1')")
    status = json.dumps({"promotion": "unknown", "authority": "unknown", "truth": "unknown", "source": "agda"})
    for rel, text in files.items():
        source = root / rel
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text, encoding="utf-8")
        stat = source.stat()
        module = rel[:-5].replace("/", ".")
        name = "oldThing" if "Round9" in rel else "knownThing"
        conn.execute(
            "INSERT INTO files VALUES(?, 'agda', ?, ?, ?, '', 1, '[]', '[]', '[]')",
            (rel, module, stat.st_mtime_ns, stat.st_size),
        )
        conn.execute(
            "INSERT INTO symbols VALUES(?, ?, 'function', 'agda', ?, ?, 3, 3, ?, '[]', '{}')",
            (module + "." + name, name, module, rel, status),
        )
    conn.commit()
    conn.close()


def _complete_narrative(index: SourceIndex) -> None:
    replace_narrative_events(
        index.connection,
        events=[],
        source_status={
            "git_commits": 1,
            "commit_history_complete": True,
            "semantic_history_linked": True,
        },
    )


def test_complete_repo_and_narrative_indexes_can_authorize_true_indexed_absence(tmp_path: Path):
    _repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as index:
        _complete_narrative(index)
        receipt = index.discovery_receipt("certainlyMissingXYZ")
    assert receipt["absence_status"] == "confirmed_no_indexed_candidate"
    assert receipt["absence_claim_permitted"] is True


def test_complete_repo_index_without_narrative_remains_search_incomplete(tmp_path: Path):
    _repo_index(tmp_path)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as index:
        receipt = index.discovery_receipt("certainlyMissingXYZ")
    assert receipt["absence_status"] == "search_incomplete"
    assert receipt["absence_claim_permitted"] is False


def test_historical_only_match_blocks_absence_but_is_hidden_from_live_search(tmp_path: Path):
    _repo_index(tmp_path, include_round=True)
    with SourceIndex(tmp_path, tmp_path / "preflight.sqlite3") as index:
        live = index.search_symbols("oldThing")
        receipt = index.discovery_receipt("oldThing")
    assert live == []
    assert receipt["absence_claim_permitted"] is False
    assert receipt["absence_status"] == "candidate_or_partial_object_exists"
    assert receipt["historical_matches"][0]["name"] == "oldThing"
