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



def test_apply_fix_requires_likely_opt_in_and_rechecks(tmp_path, capsys):
    path = write_module(
        tmp_path,
        "Apply.Record",
        """
record R : Set₁ where
  field
    witness : Set

mk : R
mk = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    assert main(
        [
            "diagnose",
            str(path),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--json",
        ]
    ) == 1
    payload = json.loads(capsys.readouterr().out)
    diagnostic = next(
        item for item in payload["diagnostics"]
        if item["code"] == "TSAGDA060"
    )
    diagnostic_id = diagnostic["id"]

    import pytest

    with pytest.raises(SystemExit):
        main(
            [
                "apply-fix",
                str(path),
                diagnostic_id,
                "--root",
                str(tmp_path),
                "--index",
                str(database),
            ]
        )
    capsys.readouterr()

    assert main(
        [
            "apply-fix",
            str(path),
            diagnostic_id,
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--allow-likely",
            "--json",
        ]
    ) == 0

    result = json.loads(capsys.readouterr().out)
    assert result["resolved"] is True
    before_counts = result["before_profile"]["counts"]
    assert before_counts["diagnostic_candidate_lookup_hits"] == 1
    assert before_counts.get("files_parsed", 0) == 0
    assert before_counts.get("diagnostics_cached", 0) == 0
    after_counts = result["after_profile"]["counts"]
    assert after_counts["files_parsed"] == 1
    source = path.read_text(encoding="utf-8")
    assert "witnes =" not in source
    assert "witness = Set" in source



def test_next_error_prefers_hard_fixable_diagnostic(tmp_path, capsys):
    path = write_module(
        tmp_path,
        "Next.Record",
        """
record R : Set₁ where
  field
    witness : Set

mk : R
mk = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    assert main(
        [
            "next-error",
            str(path),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--require-fix",
            "--json",
        ]
    ) == 0

    payload = json.loads(capsys.readouterr().out)
    diagnostic = payload["diagnostic"]
    assert payload["status"] == "diagnostic"
    assert diagnostic["code"] == "TSAGDA060"
    assert diagnostic["fixes"]
    assert diagnostic["fixes"][0]["edits"]


def test_warm_next_error_uses_compact_candidates(tmp_path, capsys):
    write_module(
        tmp_path,
        "Next.Lib",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    top = write_module(
        tmp_path,
        "Next.Top",
        """
import Next.Lib

record S : Set₁ where
  field
    carrier : Set

bad : S
bad = record { carier = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    # Prime the persistent closure and its per-module top candidates.
    assert main(
        [
            "diagnose",
            str(top),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--json",
        ]
    ) == 1
    capsys.readouterr()

    assert main(
        [
            "next-error",
            str(top),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--require-fix",
            "--json",
        ]
    ) == 0

    payload = json.loads(capsys.readouterr().out)
    counts = payload["profile"]["counts"]
    assert payload["status"] == "diagnostic"
    assert counts.get("files_parsed", 0) == 0
    assert counts.get("checker_instances", 0) == 0
    assert counts["next_error_modules_scanned"] == 2
    assert counts["next_error_candidates_decoded"] <= 2
    assert counts.get("diagnostics_cached", 0) == 0


def test_benchmark_payload_reports_slo_pass(tmp_path, capsys):
    path = write_module(tmp_path, "Slo.Top")
    database = tmp_path / ".cache" / "source-index.sqlite3"

    assert main(
        [
            "benchmark",
            str(path),
            "--root",
            str(tmp_path),
            "--index",
            str(database),
            "--runs",
            "2",
            "--max-cold-ms",
            "60000",
            "--max-warm-ms",
            "10000",
            "--json",
        ]
    ) == 0

    payload = json.loads(capsys.readouterr().out)
    assert payload["slo"]["passed"] is True
    assert payload["warm"]["all_zero_parse"] is True
    assert payload["agent_next_error"]["all_zero_parse"] is True
    assert (
        payload["agent_next_error"]["request_total"]["p95_ms"]
        <= payload["slo"]["max_next_error_ms"]
    )
