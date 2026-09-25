from __future__ import annotations

import json
import sqlite3
from pathlib import Path

from agda_preflight.interactive_cli import main


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n{body}", encoding="utf-8")
    return path


def test_diagnose_json_warm_request_reports_zero_parses(tmp_path, capsys):
    write_module(tmp_path, "Warm.Leaf")
    top = write_module(
        tmp_path,
        "Warm.Top",
        """
import Warm.Leaf
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    argv = [
        "diagnose",
        str(top),
        "--root",
        str(tmp_path),
        "--index",
        str(database),
        "--json",
    ]

    assert main(argv) == 0
    capsys.readouterr()

    assert main(argv) == 0
    payload = json.loads(capsys.readouterr().out)

    assert payload["cache_hit"] is True
    assert payload["profile"]["counts"].get("files_parsed", 0) == 0
    assert payload["profile"]["counts"].get("checker_instances", 0) == 0
    assert payload["profile"]["counts"]["modules_in_closure"] == 2



def test_benchmark_reports_zero_parse_warm_runs(tmp_path, capsys):
    write_module(tmp_path, "Bench.Leaf")
    top = write_module(
        tmp_path,
        "Bench.Top",
        """
import Bench.Leaf
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    assert main(
        [
            "benchmark",
            str(top),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--runs",
            "3",
            "--json",
        ]
    ) == 0

    payload = json.loads(capsys.readouterr().out)
    assert payload["warm"]["runs"] == 3
    assert payload["warm"]["all_zero_parse"] is True
    assert payload["warm"]["files_parsed"]["max"] == 0
    assert payload["cold"]["counts"]["files_parsed"] == 2



def test_diagnose_can_surface_last_known_semantic_catalog(tmp_path, capsys):
    top = write_module(tmp_path, "Semantic.Top")
    source_index = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "agda2lean.sqlite"

    connection = sqlite3.connect(semantic)
    connection.execute(
        """
        CREATE TABLE module_heads (
            module_name TEXT PRIMARY KEY,
            object_hash BLOB NOT NULL,
            declaration_count INTEGER NOT NULL,
            term_count INTEGER NOT NULL,
            updated_at TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        INSERT INTO module_heads(
            module_name, object_hash, declaration_count, term_count, updated_at
        ) VALUES (?, ?, ?, ?, ?)
        """,
        ("Semantic.Top", bytes.fromhex("abcd"), 3, 7, "2026-09-25T00:00:00Z"),
    )
    connection.commit()
    connection.close()

    assert main(
        [
            "diagnose",
            str(top),
            "--root",
            str(tmp_path),
            "--index",
            str(source_index),
            "--semantic-catalog",
            str(semantic),
            "--json",
        ]
    ) == 0

    payload = json.loads(capsys.readouterr().out)
    snapshot = payload["semantic"]["Semantic.Top"]
    assert snapshot["object_hash"] == "abcd"
    assert snapshot["declaration_count"] == 3
    assert snapshot["term_count"] == 7
    assert snapshot["freshness"] == "unknown"
    assert payload["profile"]["counts"]["semantic_snapshot_hits"] == 1
