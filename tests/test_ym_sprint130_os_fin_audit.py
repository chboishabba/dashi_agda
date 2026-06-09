from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint130_os_fin_audit.py"
SUMMARY_NAME = "ym_sprint130_os_fin_audit_summary.json"
REPORT_NAME = "ym_sprint130_os_fin_audit.md"
CLAY_PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"

TRUE_CANDIDATES = ("OS1", "FIN")

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint130 OS/FIN audit script is not integrated yet",
)


def run_script(out_dir: Path) -> dict[str, Any]:
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
    assert result.returncode in (0, 1), result.stdout + result.stderr

    summary_path = out_dir / SUMMARY_NAME
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*sprint130*os*fin*audit*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]
    return json.loads(summary_path.read_text(encoding="utf-8"))


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [
            nested for item in value.values() for nested in flatten_values(item)
        ]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json_text(summary)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def report_text(out_dir: Path) -> str:
    report_path = out_dir / REPORT_NAME
    if not report_path.exists():
        candidates = sorted(out_dir.glob("*sprint130*os*fin*audit*.md"))
        assert candidates, "Sprint130 audit report was not written"
        report_path = candidates[0]
    return report_path.read_text(encoding="utf-8")


def entries_for_code(summary: dict[str, Any], code: str) -> list[dict[str, Any]]:
    pattern = re.compile(rf"\b{re.escape(code)}\b")
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict) and pattern.search(json_text(item))
    ]


def bool_rows(summary: dict[str, Any], terms: tuple[str, ...]) -> list[dict[str, Any]]:
    pattern = re.compile("|".join(re.escape(term) for term in terms), re.IGNORECASE)
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and any(isinstance(value, bool) for value in item.values())
        and pattern.search(json_text(item))
    ]


def assert_code_has_true_status(summary: dict[str, Any], code: str) -> None:
    entries = entries_for_code(summary, code)
    assert entries, f"summary is missing {code}"
    assert any(
        entry.get("value") is True
        or entry.get("closed") is True
        or entry.get("complete") is True
        or entry.get("satisfied") is True
        or entry.get("candidate") is True
        or re.search(
            r"\b(true|closed|complete|satisfied|candidate|internal)\b",
            json_text(entry),
            re.IGNORECASE,
        )
        for entry in entries
    ), f"{code} is not recorded as true/internal candidate"


def assert_external_acceptance_false(summary: dict[str, Any]) -> None:
    rows = bool_rows(summary, ("external", "acceptance"))
    assert rows, "summary should expose external acceptance"
    assert any(
        row.get("value") is False
        or row.get("accepted") is False
        or row.get("external_acceptance") is False
        or row.get("externalAcceptance") is False
        or re.search(r"\b(false|blocked|open|not accepted|fail-closed)\b", json_text(row), re.IGNORECASE)
        for row in rows
    ), "external acceptance should remain false"


def assert_clay_promotion_false(text: str, summary: dict[str, Any]) -> None:
    rows = bool_rows(summary, ("clay", "promotion", "promoted"))
    assert rows, "summary should expose the Clay promotion gate"
    assert any(
        row.get("value") is False
        or row.get(CLAY_PROMOTED_NAME) is False
        or row.get("clay_promotion_flag") is False
        or row.get("clayYangMillsPromoted") is False
        for row in rows
    ), "Clay promotion should remain false"

    forbidden_patterns = (
        CLAY_PROMOTED_NAME + " = " + "tr" + "ue",
        CLAY_PROMOTED_NAME + '": ' + "tr" + "ue",
        CLAY_PROMOTED_NAME + ": " + "tr" + "ue",
    )
    for pattern in forbidden_patterns:
        assert pattern not in text


def test_sprint130_os_fin_audit_cli_writes_expected_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert (out_dir / SUMMARY_NAME).exists() or sorted(
        out_dir.glob("*sprint130*os*fin*audit*.json")
    )
    assert (out_dir / REPORT_NAME).exists() or sorted(
        out_dir.glob("*sprint130*os*fin*audit*.md")
    )
    assert "Sprint 130" in text or "Sprint130" in text


def test_sprint130_os1_and_fin_internal_candidates_are_true(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    for code in TRUE_CANDIDATES:
        assert re.search(rf"\b{code}\b", text), f"missing {code}"
        assert_code_has_true_status(summary, code)

    fin_entries = entries_for_code(summary, "FIN")
    assert any(
        re.search(r"\b(internal|candidate|assembly)\b", json_text(entry), re.IGNORECASE)
        for entry in fin_entries
    ), "FIN should be recorded as an internal candidate, not external acceptance"


def test_sprint130_external_acceptance_and_promotion_remain_false(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_external_acceptance_false(summary)
    assert_clay_promotion_false(text, summary)
    assert "fail-closed" in text.lower() or "external acceptance" in text.lower()


def test_sprint130_report_has_evidence_backed_sections(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    report = report_text(out_dir)

    headings = re.findall(r"(?m)^#{1,4}\s+(.+)$", report)
    assert len(headings) >= 4, "report should use section headings"
    for term in ("OS1", "FIN", "external acceptance", CLAY_PROMOTED_NAME):
        assert re.search(re.escape(term), report, re.IGNORECASE), f"missing report term {term}"

    evidence_lines = [
        line
        for line in report.splitlines()
        if re.search(r"\b(evidence|source|path|artifact|receipt|summary)\b", line, re.IGNORECASE)
    ]
    assert len(evidence_lines) >= 4, "report should cite evidence for audited sections"
    assert any(re.search(r"\.(agda|md|json|csv|txt)\b|DASHI/|Docs/|outputs/", line) for line in evidence_lines)
    assert_external_acceptance_false(summary)
