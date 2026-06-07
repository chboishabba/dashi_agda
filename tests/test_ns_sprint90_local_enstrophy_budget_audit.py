from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint90_local_enstrophy_budget_audit.py"
OUT_STEM = "ns_sprint90_local_enstrophy_budget_audit"

REQUIRED_ANCHORS = {
    "canonicalNSSprint90LocalEnstrophyDangerShellReductionReceipt",
    "localEnstrophyDangerShellReductionRecorded",
    "localEnstrophyDangerShellReductionBookkeepingClosed",
    "localizedEnstrophyFluxIdentityClosed",
    "dangerShellDissipationDominatesInfluxClosed",
    "pointwiseTailFromLocalDissipationClosed",
    "actualPointwiseH1TailClosureClosed",
    "independentCoefficientBudgetClosed",
    "independentEpsilonCoefficientClosed",
    "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
    "clayNavierStokesPromoted",
}


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint 90 local enstrophy budget audit script is missing"

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

    summary_candidates = sorted(out_dir.glob("*summary*.json")) or sorted(
        out_dir.glob("*.json")
    )
    assert summary_candidates, result.stdout + result.stderr
    summary = json.loads(summary_candidates[0].read_text(encoding="utf-8"))
    return out_dir, summary, output_text(out_dir, summary)


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json.dumps(summary, sort_keys=True)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".csv", ".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def csv_rows(out_dir: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(out_dir.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))
    return rows


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"true", "yes", "1", "present", "closed", "pass"}:
            return True
        if lowered in {"false", "no", "0", "absent", "open", "fail"}:
            return False
    return None


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def values_for_key_terms(summary: dict[str, Any], *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_text = str(key)
            if all(pattern.search(key_text) for pattern in patterns):
                values.append(value)
    return values


def forbidden_count(summary: dict[str, Any], text: str) -> int:
    count_values = values_for_key_terms(summary, "forbidden", "count")
    if count_values:
        numeric_counts = [int(value) for value in count_values if isinstance(value, int)]
        if numeric_counts:
            return max(numeric_counts)

    hit_values = values_for_key_terms(summary, "forbidden", "hit")
    list_hits = [value for value in hit_values if isinstance(value, list)]
    if list_hits:
        return max(len(value) for value in list_hits)

    match = re.search(r"forbidden[^0-9]{0,40}([0-9]+)", text, re.IGNORECASE)
    assert match, "audit output should expose a forbidden marker count"
    return int(match.group(1))


def test_ns_sprint90_writes_required_artifacts(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json")), "audit did not write JSON output"
    assert sorted(out_dir.glob("*.csv")), "audit did not write CSV output"
    assert sorted(out_dir.glob("*.md")), "audit did not write Markdown output"
    assert "sprint90" in text.lower() or "Sprint 90" in text


def test_ns_sprint90_required_anchors_are_present(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    rows = csv_rows(out_dir)
    combined_text = "\n".join([text, *[json_text(row) for row in rows]])

    for anchor in REQUIRED_ANCHORS:
        assert anchor in combined_text, f"missing required anchor: {anchor}"

    missing_anchor_rows = [
        row
        for row in rows
        if row.get("missing_anchors") not in {None, "", "none", "None", "NONE"}
        or row.get("present_in_receipt") == "False"
    ]
    assert not missing_anchor_rows


def test_ns_sprint90_forbidden_count_is_zero(tmp_path: Path) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    assert forbidden_count(summary, text) == 0


def test_ns_sprint90_route_is_fail_closed_or_open_and_not_promoted(
    tmp_path: Path,
) -> None:
    _out_dir, summary, text = run_audit(tmp_path)
    route_values = values_for_key_terms(summary, "route") + values_for_key_terms(
        summary, "decision"
    )
    route_text = " ".join(str(value) for value in route_values) + "\n" + text

    assert re.search(r"fail[-_ ]closed|open", route_text, re.IGNORECASE)
    assert re.search(r"not[-_ ]promoted|no promotion|promotion[^.\n]*false", route_text, re.IGNORECASE)
    assert not re.search(
        r"\b(promoted|promotion|clay[_ -]?navier[_ -]?stokes[_ -]?promoted)"
        r"\b\s*[:=]\s*(true|1|yes)\b",
        route_text,
        re.IGNORECASE,
    )


def test_ns_sprint90_clay_and_analytic_closure_flags_are_false(
    tmp_path: Path,
) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    rows = csv_rows(out_dir)

    clay_values = values_for_key_terms(summary, "clay") + [
        value
        for row in rows
        for key, value in row.items()
        if "clay" in key.lower() or "clay" in str(value).lower()
    ]
    assert clay_values, "audit should expose Clay promotion flags"
    assert not any(boolish(value) is True for value in clay_values)
    assert re.search(r"clay[^.\n]*(false|not[-_ ]promoted|no promotion)", text, re.IGNORECASE)

    analytic_flag_payload = summary.get("analytic_closure_flags")
    assert isinstance(analytic_flag_payload, dict)
    analytic_flags = list(analytic_flag_payload.values())

    assert analytic_flags, "audit should expose analytic closure flags"
    assert all(boolish(value) is False for value in analytic_flags)
