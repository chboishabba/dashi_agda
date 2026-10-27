from pathlib import Path

from agda_preflight.source_index import SourceIndex


def test_source_index_initializes_semantic_catalog_schema(tmp_path: Path):
    with SourceIndex(tmp_path, tmp_path / "index.sqlite3") as index:
        tables = {
            row[0]
            for row in index.connection.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            ).fetchall()
        }
    assert "semantic_symbols" in tables
