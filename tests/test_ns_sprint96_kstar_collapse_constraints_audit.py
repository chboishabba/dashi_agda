from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint96_kstar_collapse_constraints_audit.py"
OUT_STEM = "ns_sprint96_kstar_collapse_constraints_audit"
ROUTE_DECISION = "FAIL_CLOSED_KSTAR_COLLAPSE_CONSTRAINTS"

REQUIRED_RESIDUALS = (
    "finite-time K-star collapse mechanism",
    "compatibility with Leray energy",
    "exclusion of conditional K-star lower bound",
    "finite-time singularity extraction",
)

REQUIRED_ANCHORS = (
    "NSSprint96KStarCollapseMechanismConstraints",
    "Sprint96",
    "KStarCollapseMechanismConstraints",
    "KStarCollapseMechanismResiduals",
    "failClosedKStarCollapseConstraints",
    "FAIL_CLOSED_KSTAR_COLLAPSE_CONSTRAINTS",
    "fail_closed",
)

FALSE_FLAG_KEYS = (
    "complete",
    "clay_navier_stokes_promoted",
    "kstar_collapse_mechanism_closed",
)


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint 96 K* collapse constraints audit script is missing"

    out_dir = tmp_path / OUT_STEM
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

    json_paths = sorted(out_dir.glob("*.json"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    parts.extend(path.read_text(encoding="utf-8") for path in [*json_paths, *md_paths])
    return out_dir, summary, "\n".join(parts)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def values_for_key_terms(payload: Any, *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if all(pattern.search(str(key)) for pattern in patterns):
                values.append(value)
    return values


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().replace("-", "_").lower()
        if lowered in {"true", "1", "yes", "closed", "complete", "promoted", "accepted"}:
            return True
        if lowered in {"false", "0", "no", "open", "blocked", "not_closed", "not_promoted"}:
            return False
    return None


def assert_text_contains(text: str, needle: str) -> None:
    normalized = re.escape(needle).replace(r"\ ", r"[- _]*")
    assert re.search(normalized, text, re.IGNORECASE), needle


def test_ns_sprint96_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*96|sprint96", text, re.IGNORECASE)
    assert re.search(r"k\*|kstar|k-star", text, re.IGNORECASE)


def test_ns_sprint96_route_is_fail_closed_and_not_complete(tmp_path: Path) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    assert summary["fail_closed"] is True
    assert summary["complete"] is False
    assert summary["route_decision"] == ROUTE_DECISION
    assert "FAIL_CLOSED" in json.dumps(summary, sort_keys=True).upper() + text.upper()


def test_ns_sprint96_required_residuals_and_anchors_are_reported(tmp_path: Path) -> None:
    _out_dir, summary, text = run_audit(tmp_path)
    combined_text = json.dumps(summary, sort_keys=True) + "\n" + text

    for residual in REQUIRED_RESIDUALS:
        assert_text_contains(combined_text, residual)

    for anchor in REQUIRED_ANCHORS:
        assert_text_contains(combined_text, anchor)


def test_ns_sprint96_promotion_and_closure_flags_remain_false(tmp_path: Path) -> None:
    _out_dir, summary, _text = run_audit(tmp_path)

    for key in FALSE_FLAG_KEYS:
        assert key in summary, key
        assert summary[key] is False, key

    promotion_values = [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(summary, "promot"))
        if parsed is not None
    ]
    assert promotion_values and not any(promotion_values), promotion_values


def test_ns_sprint96_markdown_contains_blockers(tmp_path: Path) -> None:
    out_dir, _summary, _text = run_audit(tmp_path)
    markdown = "\n".join(path.read_text(encoding="utf-8") for path in sorted(out_dir.glob("*.md")))

    assert re.search(r"blocker|blocked|open gate|residual", markdown, re.IGNORECASE)
    for residual in REQUIRED_RESIDUALS:
        assert_text_contains(markdown, residual)
