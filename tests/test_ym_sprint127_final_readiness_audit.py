from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint127_final_readiness_audit.py"
SUMMARY_NAME = "ym_sprint127_final_readiness_audit_summary.json"
REPORT_NAME = "ym_sprint127_final_readiness_audit.md"
CLAY_PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"

HARD_BLOCKERS = ("CC1", "WC1", "MC1", "SC1", "SC3")
TERMINAL_BLOCKERS = ("OS1", "SY1", "GG1", "FIN")
REQUIRED_PRIOR_OUTPUTS = (
    "outputs/ym_sprint121_cc1_kernel_audit",
    "outputs/ym_sprint121_compact_group_parameter_table",
    "outputs/ym_sprint122_cc2_gauge_covariance_audit",
    "outputs/ym_sprint123_wc1_weak_compactness_audit",
    "outputs/ym_sprint124_mosco_liminf_audit",
    "outputs/ym_sprint125_log_generator_audit",
    "outputs/ym_sprint126_os_symmetry_group_audit",
)

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint127 final readiness audit script is not integrated yet",
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
        candidates = sorted(out_dir.glob("*sprint127*final*readiness*audit*.json"))
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
        if path.suffix in {".json", ".md", ".markdown", ".txt"}:
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


def assert_json_and_markdown_outputs(out_dir: Path) -> None:
    assert (out_dir / SUMMARY_NAME).exists() or sorted(
        out_dir.glob("*sprint127*final*readiness*audit*.json")
    )
    assert (out_dir / REPORT_NAME).exists() or sorted(
        out_dir.glob("*sprint127*final*readiness*audit*.md")
    )


def assert_terms_present(text: str, terms: tuple[str, ...], label: str) -> None:
    missing = [term for term in terms if not re.search(rf"\b{re.escape(term)}\b", text)]
    assert not missing, f"missing {label}: {missing}"


def assert_prior_output_inventory_present(text: str) -> None:
    missing = [path for path in REQUIRED_PRIOR_OUTPUTS if path not in text]
    assert not missing, f"artifact inventory is missing prior Sprint outputs: {missing}"


def assert_no_clay_promotion_true(text: str, summary: dict[str, Any]) -> None:
    assert all(flag["value"] is False for flag in promotion_flags(summary))
    forbidden_patterns = (
        CLAY_PROMOTED_NAME + " = " + "tr" + "ue",
        CLAY_PROMOTED_NAME + '": ' + "tr" + "ue",
        CLAY_PROMOTED_NAME + ": " + "tr" + "ue",
    )
    for pattern in forbidden_patterns:
        assert pattern not in text


def test_sprint127_final_readiness_cli_writes_json_and_markdown_outputs(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_json_and_markdown_outputs(out_dir)
    assert "Sprint 127" in text or "Sprint127" in text
    assert normalized_route_decision(summary) == "fail-closed"


def test_sprint127_final_readiness_records_exact_hard_and_terminal_blockers(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_terms_present(text, HARD_BLOCKERS, "hard blockers")
    assert_terms_present(text, TERMINAL_BLOCKERS, "terminal blockers")
    assert "fail-closed" in text.lower()


def test_sprint127_final_readiness_inventories_sprint121_to_126_artifacts(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_prior_output_inventory_present(text)
    for sprint in range(121, 127):
        assert f"Sprint{sprint}" in text or f"Sprint {sprint}" in text


def test_sprint127_final_readiness_rejects_clay_promotion_true(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_no_clay_promotion_true(text, summary)
