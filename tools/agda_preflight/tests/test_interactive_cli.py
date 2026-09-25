from __future__ import annotations

import json
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
