from __future__ import annotations

import csv
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint131_localized_viscous_comparison_audit.py"


def run_audit(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path]:
    out_dir = tmp_path / SCRIPT.stem
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )
    return result, out_dir


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def summary_json(json_paths: list[Path]) -> dict[str, Any]:
    candidates = [path for path in json_paths if "summary" in path.name.lower()]
    assert candidates, f"missing summary JSON in {[path.name for path in json_paths]}"
    payload = load_json(candidates[0])
    assert isinstance(payload, dict), f"summary is not a JSON object: {candidates[0].name}"
    return payload


def rows_text(json_paths: list[Path], csv_paths: list[Path]) -> str:
    parts: list[str] = []
    for path in json_paths:
        if "row" in path.name.lower():
            parts.append(path.read_text(encoding="utf-8"))
    for path in csv_paths:
        parts.append(path.read_text(encoding="utf-8"))
        with path.open(newline="", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))
        assert rows, f"rows CSV is empty: {path.name}"
    return "\n".join(parts)


def report_text(md_paths: list[Path]) -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in md_paths)


def combined_artifact_text(json_paths: list[Path], csv_paths: list[Path], md_paths: list[Path]) -> str:
    return "\n".join(
        [path.read_text(encoding="utf-8") for path in json_paths + csv_paths + md_paths]
    )


def has_ratio_exponent(text: str) -> bool:
    compact = re.sub(r"[\s`$\\{}()]", "", text.lower())
    return bool(
        "nu*tau^-3beta" in compact
        or "nu*tau^(-3beta)" in text.lower().replace(" ", "")
        or "nu*tau^(-3*beta)" in text.lower().replace(" ", "")
        or re.search(r"ratio[_ -]?exponent[^\\n-]*-?3\s*\*?\s*beta", text, re.IGNORECASE)
        or re.search(r"viscous/source[^\\n-]*-?3\s*\*?\s*beta", text, re.IGNORECASE)
    )


def test_sprint131_localized_viscous_comparison_script_exists() -> None:
    assert SCRIPT.exists(), f"missing audit script: {SCRIPT.relative_to(REPO_ROOT)}"


def test_sprint131_localized_viscous_comparison_cli_writes_closed_outputs(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing audit script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_audit(tmp_path)

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert result.returncode == 0, result.stdout + result.stderr
    assert json_paths, "audit did not write JSON output"
    assert csv_paths or any("row" in path.name.lower() for path in json_paths), (
        "audit did not write rows output"
    )
    assert md_paths, "audit did not write Markdown report"

    summary = summary_json(json_paths)
    assert summary["viscous_lower_comparison_closed"] is True
    assert summary["ratio_diverges"] is True
    assert summary["supports_hou_luo_ns_obstruction"] is True
    assert summary["complete"] is True
    assert summary["clay_navier_stokes_promoted"] is False


def test_sprint131_report_or_rows_record_localized_viscous_comparison_contract(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing audit script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_audit(tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    text = "\n".join((report_text(md_paths), rows_text(json_paths, csv_paths)))

    assert "LocalizedViscousLowerComparison" in text
    assert re.search(r"1\s*<\s*alpha\s*<\s*3\s*/\s*2", text, re.IGNORECASE)
    assert re.search(r"beta\s*=\s*alpha\s*-\s*1", text, re.IGNORECASE)
    assert has_ratio_exponent(text), (
        "report or rows should mention nu * tau^(-3 beta), or an equivalent "
        "ratio exponent"
    )


def test_sprint131_artifacts_do_not_promote_clay_navier_stokes(tmp_path: Path) -> None:
    assert SCRIPT.exists(), f"missing audit script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_audit(tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    text = combined_artifact_text(json_paths, csv_paths, md_paths)

    assert not re.search(
        r'"?\bclay(?:_navier_stokes)?_promoted\b"?\s*[:=]\s*(?:true|1)\b',
        text,
        re.IGNORECASE,
    )
    assert not re.search(
        r"\bclay\s+navier[- ]stokes\s+promoted\b\s*[:=]\s*(?:true|1)\b",
        text,
        re.IGNORECASE,
    )
