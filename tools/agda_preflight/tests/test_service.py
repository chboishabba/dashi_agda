from __future__ import annotations

import hashlib
import io
import json
import sqlite3
import textwrap
from pathlib import Path

from agda_preflight.service import DashiAgdaService, serve_streams


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


def test_service_warm_next_error_stays_zero_parse(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Record",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
    ) as service:
        first = service.next_error(
            str(path),
            require_fix=True,
        )
        assert first["status"] == "diagnostic"

        second = service.next_error(
            str(path),
            require_fix=True,
        )

    counts = second["profile"]["counts"]
    assert second["status"] == "diagnostic"
    assert counts.get("files_parsed", 0) == 0
    assert counts.get("checker_instances", 0) == 0
    assert counts["next_error_candidates_decoded"] == 1


def test_service_observes_edit_between_requests(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Edit",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
    ) as service:
        first = service.next_error(
            str(path),
            require_fix=True,
        )
        assert first["status"] == "diagnostic"

        path.write_text(
            """module Service.Edit where

record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witness = Set }

extra : Set
extra = Set
""",
            encoding="utf-8",
        )

        second = service.next_error(
            str(path),
            require_fix=True,
        )

    assert second["status"] == "clean"
    assert second["profile"]["counts"]["files_parsed"] == 1


def test_service_next_error_apply_fix_loop(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Apply",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
    ) as service:
        first = service.next_error(
            str(path),
            require_fix=True,
        )
        diagnostic = first["diagnostic"]
        assert diagnostic is not None

        applied = service.apply_fix(
            str(path),
            diagnostic["id"],
            allow_likely=True,
        )
        assert applied["resolved"] is True

        final = service.next_error(
            str(path),
            require_fix=True,
        )

    assert final["status"] == "clean"
    source = path.read_text(encoding="utf-8")
    assert "witnes =" not in source
    assert "witness = Set" in source


def test_jsonl_service_protocol_roundtrip(tmp_path):
    path = write_module(tmp_path, "Service.Protocol")
    database = tmp_path / ".cache" / "source-index.sqlite3"

    requests = io.StringIO(
        "\n".join(
            [
                json.dumps(
                    {
                        "id": 1,
                        "method": "cache_status",
                        "params": {},
                    }
                ),
                json.dumps(
                    {
                        "id": 2,
                        "method": "next_error",
                        "params": {"target": str(path)},
                    }
                ),
                json.dumps(
                    {
                        "id": 3,
                        "method": "shutdown",
                        "params": {},
                    }
                ),
            ]
        )
        + "\n"
    )
    output = io.StringIO()

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
    ) as service:
        serve_streams(service, requests, output)

    responses = [
        json.loads(line)
        for line in output.getvalue().splitlines()
    ]
    assert [item["id"] for item in responses] == [1, 2, 3]
    assert all(item["ok"] for item in responses)
    assert responses[1]["result"]["status"] == "clean"
    assert responses[2]["result"]["status"] == "shutdown"



def _write_semantic_catalog(path, module_name, checked_hash):
    connection = sqlite3.connect(path)
    connection.execute(
        """
        CREATE TABLE module_heads (
            module_name TEXT PRIMARY KEY,
            object_hash BLOB NOT NULL,
            declaration_count INTEGER NOT NULL,
            term_count INTEGER NOT NULL,
            checked_source_sha256 TEXT,
            updated_at TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        INSERT INTO module_heads(
            module_name, object_hash, declaration_count, term_count,
            checked_source_sha256, updated_at
        ) VALUES (?, ?, ?, ?, ?, ?)
        """,
        (
            module_name,
            bytes.fromhex("abcd"),
            1,
            2,
            checked_hash,
            "2026-09-26T00:00:00Z",
        ),
    )
    connection.commit()
    connection.close()


def _write_fake_promoter(path: Path, *, update_catalog: bool) -> None:
    update = (
        """
connection = sqlite3.connect(catalog)
connection.execute(
    "CREATE TABLE IF NOT EXISTS module_heads ("
    "module_name TEXT PRIMARY KEY, "
    "object_hash BLOB NOT NULL, "
    "declaration_count INTEGER NOT NULL, "
    "term_count INTEGER NOT NULL, "
    "checked_source_sha256 TEXT, "
    "updated_at TEXT NOT NULL)"
)
connection.execute(
    "INSERT INTO module_heads("
    "module_name, object_hash, declaration_count, term_count, "
    "checked_source_sha256, updated_at"
    ") VALUES (?, ?, ?, ?, ?, ?) "
    "ON CONFLICT(module_name) DO UPDATE SET "
    "object_hash = excluded.object_hash, "
    "declaration_count = excluded.declaration_count, "
    "term_count = excluded.term_count, "
    "checked_source_sha256 = excluded.checked_source_sha256, "
    "updated_at = excluded.updated_at",
    (module, bytes.fromhex("abcd"), 1, 2, source_hash, "2026-09-27T00:00:00Z"),
)
connection.commit()
connection.close()
"""
        if update_catalog
        else ""
    )

    path.write_text(
        textwrap.dedent(
            f"""\
            #!/usr/bin/env python3
            import hashlib
            import json
            from pathlib import Path
            import sqlite3
            import sys

            source = Path(sys.argv[1])
            module = sys.argv[2]
            catalog = Path(sys.argv[3])
            receipt = Path(sys.argv[4])
            source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
            {update}
            receipt.parent.mkdir(parents=True, exist_ok=True)
            receipt.write_text(
                json.dumps({{
                    "status": "promoter-finished",
                    "module": module,
                    "source_sha256": source_hash,
                }}),
                encoding="utf-8",
            )
            """
        ),
        encoding="utf-8",
    )
    path.chmod(0o755)


def test_service_promote_requires_fresh_catalog_postcondition(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Promote",
        "x : Set\nx = Set\n",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "semantic.sqlite"
    promoter = tmp_path / "fake-promoter"
    _write_fake_promoter(promoter, update_catalog=True)

    command = (
        f"{promoter} {{file}} {{module}} {{catalog}} {{receipt}}"
    )
    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
        promoter_command=command,
    ) as service:
        result = service.promote(str(path))

    expected_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    assert result["status"] == "promoted"
    assert result["semantic_freshness"] == "fresh"
    assert result["source_sha256"] == expected_hash
    assert result["semantic"]["checked_source_sha256"] == expected_hash
    assert result["promoter_receipt"]["status"] == "promoter-finished"
    assert result["receipt_id"] > 0


def test_service_promote_exit_zero_without_fresh_head_is_unverified(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Unverified",
        "x : Set\nx = Set\n",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "semantic.sqlite"
    promoter = tmp_path / "fake-promoter"
    _write_fake_promoter(promoter, update_catalog=False)

    command = (
        f"{promoter} {{file}} {{module}} {{catalog}} {{receipt}}"
    )
    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
        promoter_command=command,
    ) as service:
        result = service.promote(str(path))

    assert result["promoter_returncode"] == 0
    assert result["status"] == "unverified"
    assert result["semantic_freshness"] == "unknown"


def test_promotion_history_survives_service_restart(tmp_path):
    path = write_module(
        tmp_path,
        "Service.History",
        "x : Set\nx = Set\n",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "semantic.sqlite"
    promoter = tmp_path / "fake-promoter"
    _write_fake_promoter(promoter, update_catalog=True)
    command = (
        f"{promoter} {{file}} {{module}} {{catalog}} {{receipt}}"
    )

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
        promoter_command=command,
    ) as service:
        promoted = service.promote(str(path))
        receipt_id = promoted["receipt_id"]

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
    ) as service:
        history = service.promotion_history(
            module_name="Service.History",
        )

    assert len(history["receipts"]) == 1
    receipt = history["receipts"][0]
    assert receipt["receipt_id"] == receipt_id
    assert receipt["status"] == "promoted"
    assert receipt["semantic_freshness"] == "fresh"


def test_service_semantic_status_transitions_fresh_to_stale(tmp_path):
    path = write_module(
        tmp_path,
        "Service.Semantic",
        "x : Set\nx = Set\n",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "agda2lean.sqlite"
    checked_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    _write_semantic_catalog(
        semantic,
        "Service.Semantic",
        checked_hash,
    )

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
    ) as service:
        # Populate the source index once.
        service.diagnose(str(path))

        fresh = service.semantic_status(str(path))
        assert fresh["fresh"] == 1
        assert fresh["stale"] == 0
        assert fresh["snapshots"]["Service.Semantic"]["freshness"] == "fresh"

        path.write_text(
            "module Service.Semantic where\nx : Set\nx = (λ A → A) Set\n",
            encoding="utf-8",
        )

        stale = service.semantic_status(str(path))
        assert stale["fresh"] == 0
        assert stale["stale"] == 1
        assert stale["snapshots"]["Service.Semantic"]["freshness"] == "stale"


def test_service_next_error_includes_module_semantic_freshness(tmp_path):
    path = write_module(
        tmp_path,
        "Service.SemanticError",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    semantic = tmp_path / "agda2lean.sqlite"
    checked_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    _write_semantic_catalog(
        semantic,
        "Service.SemanticError",
        checked_hash,
    )

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=2,
        semantic_catalog=semantic,
    ) as service:
        result = service.next_error(
            str(path),
            require_fix=True,
        )

    assert result["status"] == "diagnostic"
    snapshot = result["semantic"]["Service.SemanticError"]
    assert snapshot["freshness"] == "fresh"
    assert snapshot["checked_source_sha256"] == checked_hash
