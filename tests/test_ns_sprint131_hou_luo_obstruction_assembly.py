from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint131_hou_luo_obstruction_assembly.py"
STEM = "ns_sprint131_hou_luo_obstruction_assembly"
SUMMARY_NAME = f"{STEM}_summary.json"
ROWS_NAME = f"{STEM}_rows.json"
REPORT_NAME = f"{STEM}.md"

EXPECTED_SUMMARY_FLAGS = {
    "candidate_scaling_formalized": True,
    "axis_boundary_conditions_recorded": True,
    "hou_luo_ns_obstruction_theorem": True,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
    "complete": True,
}

REQUIRED_LEMMAS = (
    "CandidateScalingHypothesisFormalization",
    "RigorousSourceUpperBound",
    "LocalizedViscousLowerComparison",
    "AxisBoundaryRegularityConditions",
    "AxisymmetricHouLuoNSViscousDominanceObstruction",
)

PROMOTION_TRUE_PATTERNS = (
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true', re.IGNORECASE),
    re.compile(r'"full_clay_ns_solved"\s*:\s*true', re.IGNORECASE),
    re.compile(
        r"\bclay[_\s-]*(?:navier[_\s-]*stokes[_\s-]*)?promot\w*\b\s*(?:[:=]|\|)\s*true\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\btrue\s*(?:[:=]|\|)\s*clay[_\s-]*(?:navier[_\s-]*stokes[_\s-]*)?promot\w*\b",
        re.IGNORECASE,
    ),
)


def run_assembly(out_dir: Path) -> tuple[dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), f"missing Sprint 131 Hou-Luo obstruction assembly script: {SCRIPT}"

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    summary_path = out_dir / SUMMARY_NAME
    rows_path = out_dir / ROWS_NAME
    report_path = out_dir / REPORT_NAME

    assert summary_path.is_file(), f"summary JSON was not written: {summary_path}"
    assert rows_path.is_file(), f"rows JSON was not written: {rows_path}"
    assert report_path.is_file(), f"Markdown report was not written: {report_path}"
    assert summary_path.stat().st_size > 0
    assert rows_path.stat().st_size > 0
    assert report_path.stat().st_size > 0

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    rows = load_rows(rows_path)
    artifact_text = "\n".join(
        [
            result.stdout,
            result.stderr,
            json.dumps(summary, sort_keys=True),
            json.dumps(rows, sort_keys=True),
            report_path.read_text(encoding="utf-8"),
        ]
    )
    return summary, rows, artifact_text


def load_rows(rows_path: Path) -> list[dict[str, Any]]:
    payload = json.loads(rows_path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        assert all(isinstance(row, dict) for row in payload)
        return payload
    if isinstance(payload, dict) and isinstance(payload.get("rows"), list):
        rows = payload["rows"]
        assert all(isinstance(row, dict) for row in rows)
        return rows
    raise AssertionError(f"rows JSON should be a list or contain rows list: {rows_path}")


def test_sprint131_hou_luo_script_exists_and_cli_writes_artifacts(tmp_path: Path) -> None:
    out_dir = tmp_path / STEM
    summary, rows, artifact_text = run_assembly(out_dir)

    assert isinstance(summary, dict) and summary
    assert rows, "assembly should write nonempty obstruction rows"
    assert "Hou" in artifact_text or "Luo" in artifact_text


def test_sprint131_hou_luo_summary_records_closed_obstruction_without_clay_promotion(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / STEM
    summary, _rows, artifact_text = run_assembly(out_dir)

    for key, expected in EXPECTED_SUMMARY_FLAGS.items():
        assert summary.get(key) is expected, key
    for pattern in PROMOTION_TRUE_PATTERNS:
        assert not pattern.search(artifact_text), pattern.pattern


def test_sprint131_hou_luo_rows_or_report_name_required_lemmas(tmp_path: Path) -> None:
    out_dir = tmp_path / STEM
    _summary, rows, artifact_text = run_assembly(out_dir)

    rows_and_report_text = json.dumps(rows, sort_keys=True) + "\n" + artifact_text
    for lemma in REQUIRED_LEMMAS:
        assert lemma in rows_and_report_text, lemma
