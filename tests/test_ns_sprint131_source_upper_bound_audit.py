from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

AUDIT_ID = "ns_sprint131_source_upper_bound_audit"
SCRIPT = SCRIPT_DIR / f"{AUDIT_ID}.py"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
ROWS_NAME = f"{AUDIT_ID}_rows.json"
REPORT_NAME = f"{AUDIT_ID}.md"

REQUIRED_MARKERS = (
    "RigorousSourceUpperBound",
    "partial_z(u1^2)=2 u1 partial_z u1",
    "M0",
    "delta=tau^beta",
)


def artifact_text(*paths: Path) -> str:
    return "\n".join(path.read_text(encoding="utf-8", errors="replace") for path in paths)


def payload_text(*payloads: Any) -> str:
    return json.dumps(payloads, sort_keys=True)


def run_audit(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], dict[str, Any], Any, str]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

    out_dir = tmp_path / AUDIT_ID
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    summary_path = out_dir / SUMMARY_NAME
    rows_path = out_dir / ROWS_NAME
    report_path = out_dir / REPORT_NAME
    output_text = "\n".join(
        (
            result.stdout,
            result.stderr,
            artifact_text(
                *[path for path in (summary_path, rows_path, report_path) if path.is_file()]
            ),
        )
    )

    assert summary_path.is_file(), output_text
    assert rows_path.is_file(), output_text
    assert report_path.is_file(), output_text

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    rows = json.loads(rows_path.read_text(encoding="utf-8"))
    return result, summary, rows, output_text


def test_sprint131_source_upper_bound_audit_script_exists() -> None:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))


def test_sprint131_cli_writes_summary_rows_report_and_exits_0(tmp_path: Path) -> None:
    result, _summary, _rows, output_text = run_audit(tmp_path)

    assert result.returncode == 0, output_text


def test_sprint131_summary_closes_source_upper_bound_without_clay_promotion(
    tmp_path: Path,
) -> None:
    result, summary, _rows, output_text = run_audit(tmp_path)
    assert result.returncode == 0, output_text

    assert summary["source_upper_bound_closed"] is True
    assert summary["uses_u1_maximum_principle"] is True
    assert summary["quadratic_source_obstructed"] is True
    assert summary["complete"] is True
    assert summary["clay_navier_stokes_promoted"] is False


def test_sprint131_report_or_json_records_required_source_bound_markers(
    tmp_path: Path,
) -> None:
    result, summary, rows, output_text = run_audit(tmp_path)
    assert result.returncode == 0, output_text

    combined_text = payload_text(summary, rows) + "\n" + output_text
    for marker in REQUIRED_MARKERS:
        assert marker in combined_text, marker


def test_sprint131_has_no_clay_promotion_true_anywhere(tmp_path: Path) -> None:
    result, summary, rows, output_text = run_audit(tmp_path)
    assert result.returncode == 0, output_text

    combined_text = payload_text(summary, rows) + "\n" + output_text
    assert summary["clay_navier_stokes_promoted"] is False
    assert not re.search(
        r'"clay_navier_stokes_promoted"\s*:\s*true',
        combined_text,
        re.IGNORECASE,
    )
    assert not re.search(
        r"\bclay\s+navier[- ]stokes\s+promoted\s*[:=]\s*`?true`?",
        combined_text,
        re.IGNORECASE,
    )
