from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint91_localized_flux_identity_audit.py"
OUT_STEM = "ns_sprint91_localized_flux_identity_audit"

REQUIRED_ANCHORS = {
    "canonicalNSSprint91LocalizedFluxIdentityAndCoefficientBudget",
    "LocalizedFluxIdentityImportedFromFixedKLP",
    "canonicalLocalizedFluxIdentityImportedFromFixedKLP",
    "Sprint91ClosedBookkeeping",
    "canonicalSprint91ClosedBookkeeping",
    "fullFixedKLPIdentityImported",
    "localizedFluxIdentityBookedAtFixedK",
    "localizedEnstrophyFluxIdentityClosed",
    "dangerShellDissipationDominatesInfluxClosed",
    "pointwiseTailFromLocalDissipationClosed",
    "independentCoefficientBudgetClosed",
    "clayNavierStokesPromoted",
}


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint 91 localized flux identity audit script is missing"

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


def values_for_key_terms(summary: dict[str, Any], *terms: str) -> list[Any]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    values: list[Any] = []
    for item in flatten(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if all(pattern.search(str(key)) for pattern in patterns):
                values.append(value)
    return values


def named_bool_values(summary: dict[str, Any], text: str, *terms: str) -> list[bool]:
    values = [boolish(value) for value in values_for_key_terms(summary, *terms)]
    values = [value for value in values if value is not None]
    pattern = re.compile(
        r"[\w -]*".join(re.escape(term) for term in terms)
        + r"[\w -]{0,80}[:=]\s*(true|false|yes|no|0|1)\b",
        re.IGNORECASE,
    )
    for match in pattern.finditer(text):
        parsed = boolish(match.group(1))
        if parsed is not None:
            values.append(parsed)
    return values


def forbidden_count(summary: dict[str, Any], text: str) -> int:
    count_values = values_for_key_terms(summary, "forbidden", "count")
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


def assert_named_bool(
    summary: dict[str, Any],
    text: str,
    terms: tuple[str, ...],
    expected: bool,
) -> None:
    values = named_bool_values(summary, text, *terms)
    assert values, f"missing bool evidence for {'/'.join(terms)}"
    assert expected in values
    assert not any(value is not expected for value in values)


def test_ns_sprint91_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json")), "audit did not write JSON output"
    assert sorted(out_dir.glob("*.csv")), "audit did not write CSV output"
    assert sorted(out_dir.glob("*.md")), "audit did not write Markdown output"
    assert "sprint91" in text.lower() or "Sprint 91" in text


def test_ns_sprint91_required_anchors_present_and_forbidden_count_zero(
    tmp_path: Path,
) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    rows = csv_rows(out_dir)
    combined_text = "\n".join([text, *[json.dumps(row, sort_keys=True) for row in rows]])

    for anchor in REQUIRED_ANCHORS:
        assert anchor in combined_text, f"missing required anchor: {anchor}"

    missing_anchor_rows = [
        row
        for row in rows
        if row.get("missing_anchors") not in {None, "", "none", "None", "NONE"}
        or row.get("present_in_receipt") == "False"
    ]
    assert not missing_anchor_rows
    assert forbidden_count(summary, combined_text) == 0


def test_ns_sprint91_identity_bookkeeping_closed_but_analytic_closures_open(
    tmp_path: Path,
) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    assert_named_bool(summary, text, ("localized", "enstrophy", "flux", "identity", "closed"), True)
    assert_named_bool(summary, text, ("dominance", "gate", "closed"), False)
    assert_named_bool(summary, text, ("pointwise", "gate", "closed"), False)
    assert_named_bool(summary, text, ("independent", "coefficient", "budget", "closed"), False)


def test_ns_sprint91_route_open_or_fail_closed_and_not_promoted(
    tmp_path: Path,
) -> None:
    _out_dir, summary, text = run_audit(tmp_path)
    route_values = values_for_key_terms(summary, "route") + values_for_key_terms(
        summary, "decision"
    )
    route_text = " ".join(str(value) for value in route_values) + "\n" + text

    assert re.search(r"fail[-_ ]closed|open", route_text, re.IGNORECASE)
    assert re.search(
        r"not[-_ ]promoted|no promotion|promotion[^.\n]*false",
        route_text,
        re.IGNORECASE,
    )
    assert not re.search(
        r"\b(promoted|promotion|clay[_ -]?navier[_ -]?stokes[_ -]?promoted)"
        r"\b\s*[:=]\s*(true|1|yes)\b",
        route_text,
        re.IGNORECASE,
    )
    assert_named_bool(summary, text, ("clay", "promoted"), False)
