from __future__ import annotations

import io
import json
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
