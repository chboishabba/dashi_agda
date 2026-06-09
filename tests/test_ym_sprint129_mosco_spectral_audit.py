from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint129_mosco_spectral_audit.py"
SUMMARY_NAME = "ym_sprint129_mosco_spectral_audit_summary.json"
REPORT_NAME = "ym_sprint129_mosco_spectral_audit.md"
CLAY_PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"

TRUE_GATES = ("MC1", "MC2", "MC3", "MC4", "SC2")
REMAINING_BLOCKERS = ("OS1", "FIN")

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint129 Mosco spectral audit script is not integrated yet",
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
        candidates = sorted(out_dir.glob("*sprint129*mosco*spectral*audit*.json"))
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


def normalized_route_decision(summary: dict[str, Any]) -> str:
    for item in flatten_values(summary):
        if isinstance(item, dict):
            for key, value in item.items():
                if "route" in str(key).lower() and "decision" in str(key).lower():
                    return str(value).lower().replace("_", "-")
        elif isinstance(item, str) and "fail-closed" in item.lower():
            return "fail-closed"
    return ""


def promotion_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    flags = [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and "value" in item
        and isinstance(item.get("value"), bool)
        and re.search(r"clay|promotion|promoted", json_text(item), re.IGNORECASE)
    ]
    if not flags:
        flags = [
            item
            for item in flatten_values(summary)
            if isinstance(item, dict)
            and set(item) >= {"name", "value"}
            and isinstance(item.get("value"), bool)
            and re.search(r"clay|promotion|promoted", str(item["name"]), re.IGNORECASE)
        ]
    assert flags, "summary should expose the Clay promotion gate"
    return flags


def entries_for_code(summary: dict[str, Any], code: str) -> list[dict[str, Any]]:
    pattern = re.compile(rf"\b{re.escape(code)}\b")
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict) and pattern.search(json_text(item))
    ]


def assert_terms_present(text: str, terms: tuple[str, ...], label: str) -> None:
    missing = [term for term in terms if not re.search(rf"\b{re.escape(term)}\b", text)]
    assert not missing, f"missing {label}: {missing}"


def assert_code_has_true_status(summary: dict[str, Any], code: str) -> None:
    entries = entries_for_code(summary, code)
    assert entries, f"summary is missing {code}"
    assert any(
        entry.get("value") is True
        or entry.get("closed") is True
        or entry.get("complete") is True
        or entry.get("satisfied") is True
        or re.search(r"\b(true|closed|complete|satisfied|discharged)\b", json_text(entry), re.IGNORECASE)
        for entry in entries
    ), f"{code} is not recorded as true/closed"


def assert_code_has_blocker_status(summary: dict[str, Any], code: str) -> None:
    entries = entries_for_code(summary, code)
    assert entries, f"summary is missing {code}"
    assert any(
        entry.get("value") is False
        or entry.get("blocked") is True
        or re.search(r"\b(blocker|blocked|open|remaining|false)\b", json_text(entry), re.IGNORECASE)
        for entry in entries
    ), f"{code} is not recorded as a remaining blocker"


def assert_no_clay_promotion_true(text: str, summary: dict[str, Any]) -> None:
    assert all(flag["value"] is False for flag in promotion_flags(summary))
    forbidden_patterns = (
        CLAY_PROMOTED_NAME + " = " + "tr" + "ue",
        CLAY_PROMOTED_NAME + '": ' + "tr" + "ue",
        CLAY_PROMOTED_NAME + ": " + "tr" + "ue",
    )
    for pattern in forbidden_patterns:
        assert pattern not in text


def test_sprint129_mosco_spectral_audit_cli_writes_expected_outputs(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert (out_dir / SUMMARY_NAME).exists() or sorted(
        out_dir.glob("*sprint129*mosco*spectral*audit*.json")
    )
    assert (out_dir / REPORT_NAME).exists() or sorted(
        out_dir.glob("*sprint129*mosco*spectral*audit*.md")
    )
    assert "Sprint 129" in text or "Sprint129" in text
    assert normalized_route_decision(summary) == "fail-closed"


def test_sprint129_mosco_spectral_audit_records_true_mc_and_sc2_gates(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_terms_present(text, TRUE_GATES, "true Mosco/spectral gates")
    for code in TRUE_GATES:
        assert_code_has_true_status(summary, code)


def test_sprint129_mosco_spectral_audit_records_os1_and_fin_blockers(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_terms_present(text, REMAINING_BLOCKERS, "remaining blockers")
    for code in REMAINING_BLOCKERS:
        assert_code_has_blocker_status(summary, code)
    assert "fail-closed" in text.lower()


def test_sprint129_mosco_spectral_audit_rejects_clay_promotion_true(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_no_clay_promotion_true(text, summary)
