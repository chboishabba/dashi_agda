import sqlite3
from pathlib import Path

from agda_preflight.semantic_catalog import SemanticCatalog


def _catalog(path: Path):
    conn = sqlite3.connect(path)
    conn.executescript(
        """
        CREATE TABLE module_heads(
          module_name TEXT PRIMARY KEY,
          object_hash BLOB NOT NULL,
          declaration_count INTEGER NOT NULL,
          term_count INTEGER NOT NULL,
          checked_source_sha256 TEXT,
          updated_at TEXT NOT NULL
        );
        CREATE TABLE declarations(
          declaration_name TEXT PRIMARY KEY,
          module_name TEXT NOT NULL,
          role TEXT NOT NULL,
          mapping_mode TEXT NOT NULL,
          type_term_id INTEGER NOT NULL,
          body_term_id INTEGER,
          source_file TEXT NOT NULL,
          source_start_line INTEGER NOT NULL,
          source_end_line INTEGER NOT NULL
        );
        CREATE TABLE direct_dependencies(
          declaration_name TEXT NOT NULL,
          dependency_name TEXT NOT NULL,
          PRIMARY KEY(declaration_name, dependency_name)
        );
        """
    )
    conn.execute(
        "INSERT INTO module_heads VALUES(?, ?, 1, 4, ?, 'now')",
        ("DASHI.Example", bytes.fromhex("12" * 32), "a" * 64),
    )
    conn.execute(
        "INSERT INTO declarations VALUES(?, ?, 'Theorem', 'Reconstruct', 1, 2, ?, 7, 9)",
        ("DASHI.Example.sourceTheorem", "DASHI.Example", "DASHI/Example.agda"),
    )
    conn.execute(
        "INSERT INTO direct_dependencies VALUES(?, ?)",
        ("DASHI.Example.sourceTheorem", "DASHI.Core.helper"),
    )
    conn.commit()
    conn.close()


def test_declaration_capability_exposes_mapping_freshness_and_dependencies(tmp_path: Path):
    database = tmp_path / "catalog.sqlite3"
    _catalog(database)
    with SemanticCatalog(database) as catalog:
        item = catalog.declaration_capability(
            "DASHI.Example.sourceTheorem",
            current_source_hash="a" * 64,
        )

    assert item["declaration_name"] == "DASHI.Example.sourceTheorem"
    assert item["module_name"] == "DASHI.Example"
    assert item["role"] == "Theorem"
    assert item["mapping_mode"] == "Reconstruct"
    assert item["object_hash"] == "12" * 32
    assert item["freshness"] == "fresh"
    assert item["source_file"] == "DASHI/Example.agda"
    assert item["source_start_line"] == 7
    assert item["source_end_line"] == 9
    assert item["direct_dependencies"] == ["DASHI.Core.helper"]


def test_declaration_capability_returns_none_for_unknown_name(tmp_path: Path):
    database = tmp_path / "catalog.sqlite3"
    _catalog(database)
    with SemanticCatalog(database) as catalog:
        assert catalog.declaration_capability("DASHI.Missing.nope") is None
