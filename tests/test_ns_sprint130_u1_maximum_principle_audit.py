from __future__ import annotations

import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

AUDIT_ID = "ns_sprint130_u1_maximum_principle_audit"
SCRIPT = SCRIPT_DIR / f"{AUDIT_ID}.py"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
ROWS_NAME = f"{AUDIT_ID}_rows.json"
REPORT_NAME = f"{AUDIT_ID}.md"


def json_values(payload: Any) -> Iterable[Any]:
    if isinstance(payload, dict):
        yield payload
        for value in payload.values():
            yield from json_values(value)
    elif isinstance(payload, list):
        for value in payload:
            yield from json_values(value)
    else:
        yield payload


def payload_text(*payloads: Any) -> str:
    return json.dumps(payloads, sort_keys=True)


def artifact_text(*paths: Path) -> str:
    return "\n".join(path.read_text(encoding="utf-8", errors="replace") for path in paths)


def bool_values_for_keys_containing(payload: Any, *terms: str) -> list[bool]:
    values: list[bool] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if not isinstance(value, bool):
                continue
            key_text = str(key).lower()
            if all(term in key_text for term in folded_terms):
                values.append(value)
    return values


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


def test_sprint130_u1_maximum_principle_audit_script_exists() -> None:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))


def test_sprint130_cli_writes_summary_rows_report_and_exits_0(tmp_path: Path) -> None:
    result, _summary, _rows, output_text = run_audit(tmp_path)

    assert result.returncode == 0, output_text


def test_sprint130_summary_records_u1_maximum_principle_contract(tmp_path: Path) -> None:
    result, summary, _rows, output_text = run_audit(tmp_path)
    assert result.returncode == 0, output_text

    summary_text = payload_text(summary)
    assert "PureDiffusionU1MaximumPrinciple" in summary_text
    assert "weighted_measure" in summary_text or "r^3 dr dz" in summary_text
    assert "negative_semidefinite" in summary_text
    assert re.search(r'"u1_linf_nonincreasing"\s*:\s*true', summary_text), summary_text
    assert "M0" in summary_text
    assert "no_hidden_source" in summary_text
    assert re.search(r'"clay_navier_stokes_promoted"\s*:\s*false', summary_text), summary_text


def test_sprint130_has_no_clay_promotion_true_anywhere(tmp_path: Path) -> None:
    result, summary, rows, output_text = run_audit(tmp_path)
    assert result.returncode == 0, output_text

    payloads = [summary, rows]
    clay_values = bool_values_for_keys_containing(payloads, "clay")
    assert clay_values and not any(clay_values), output_text
    assert not re.search(r"clay[A-Za-z0-9_]*\s*[:=]\s*true", output_text)
    assert not re.search(r'"clay[A-Za-z0-9_]*"\s*:\s*true', output_text)
    assert not re.search(
        r"\bclay\b[^\n\r:={]*\bpromoted\b[^\n\r:={]*[:=]\s*`?true`?",
        output_text,
        re.IGNORECASE,
    )
