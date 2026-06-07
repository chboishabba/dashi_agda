from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint89_circularity_matrix_audit.py"
OUT_STEM = "ns_sprint89_circularity_matrix_audit"


def run_audit(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint 89 circularity matrix audit script is missing"

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

    summary_path = out_dir / f"{OUT_STEM}_summary.json"
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*summary*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    return out_dir, summary, output_text(out_dir, summary)


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json.dumps(summary, sort_keys=True)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".csv", ".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [
            nested for item in value.values() for nested in flatten_values(item)
        ]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def csv_rows(out_dir: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(out_dir.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                rows.append({"_csv_name": path.name, **row})
    return rows


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"true", "yes", "1", "present", "closed"}:
            return True
        if lowered in {"false", "no", "0", "absent", "open"}:
            return False
    return None


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def entries_matching(summary: dict[str, Any], *terms: str) -> list[dict[str, Any]]:
    patterns = [re.compile(re.escape(term), re.IGNORECASE) for term in terms]
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and all(pattern.search(json_text(item)) for pattern in patterns)
    ]


def assert_term_row(text: str, rows: list[dict[str, str]], *terms: str) -> None:
    pattern = re.compile(".*".join(re.escape(term) for term in terms), re.IGNORECASE)
    row_hits = [row for row in rows if pattern.search(json_text(row))]
    assert row_hits or pattern.search(text), f"missing row/text for terms: {terms}"


def assert_any_term_row(
    text: str, rows: list[dict[str, str]], term_groups: tuple[tuple[str, ...], ...]
) -> None:
    for terms in term_groups:
        pattern = re.compile(".*".join(re.escape(term) for term in terms), re.IGNORECASE)
        if any(pattern.search(json_text(row)) for row in rows) or pattern.search(text):
            return
    raise AssertionError(f"missing row/text for any term group: {term_groups}")


def test_ns_sprint89_audit_writes_summary_report_and_tables(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)

    assert summary.get("contract") in {
        OUT_STEM,
        "ns_sprint89_circularity_matrix_audit",
    }
    assert sorted(out_dir.glob("*.json")), "audit did not write a JSON summary"
    assert sorted(out_dir.glob("*.md")), "audit did not write a Markdown report"
    assert sorted(out_dir.glob("*.csv")), "audit did not write CSV tables"
    assert "Sprint 89" in text or "sprint89" in text.lower()


def test_ns_sprint89_forbidden_dependencies_are_detected(tmp_path: Path) -> None:
    out_dir, summary, text = run_audit(tmp_path)
    rows = csv_rows(out_dir)

    assert re.search(r"forbidden[-_ ]depend", text, re.IGNORECASE)
    forbidden_rows = [
        row
        for row in rows
        if re.search(r"forbidden", json_text(row), re.IGNORECASE)
        and re.search(r"depend", json_text(row), re.IGNORECASE)
    ]
    summary_rows = entries_matching(summary, "forbidden", "depend")
    assert forbidden_rows or summary_rows, "expected forbidden-dependency audit rows"

    combined_rows = forbidden_rows + [
        {key: value for key, value in row.items()} for row in summary_rows
    ]
    assert any(
        any(boolish(value) is True for value in row.values())
        or re.search(r"\b(present|detected|blocked|fail[-_ ]closed)\b", json_text(row), re.IGNORECASE)
        for row in combined_rows
    ), "forbidden dependencies should be present/detected, not silently absent"


def test_ns_sprint89_candidate_rows_cover_expected_blockers(tmp_path: Path) -> None:
    out_dir, _summary, text = run_audit(tmp_path)
    rows = csv_rows(out_dir)

    expected_terms = (
        (("Leray",),),
        (("KStar",), ("K*",)),
        (("time", "integrated"),),
        (("danger", "shell"),),
        (("coefficient",),),
    )
    for term_groups in expected_terms:
        assert_any_term_row(text, rows, term_groups)

    candidate_rows = [
        row
        for row in rows
        if re.search(r"candidate|row|blocker|dependency|obligation", json_text(row), re.IGNORECASE)
    ]
    assert len(candidate_rows) >= 5, "expected matrix candidate rows for the blockers"


def test_ns_sprint89_route_decision_stays_fail_closed_or_open(
    tmp_path: Path,
) -> None:
    _out_dir, summary, text = run_audit(tmp_path)

    route_values = [
        value
        for item in flatten_values(summary)
        if isinstance(item, dict)
        for key, value in item.items()
        if re.search(r"route|decision|promot", str(key), re.IGNORECASE)
    ]
    route_text = " ".join(str(value) for value in route_values) + "\n" + text

    assert re.search(r"fail[-_ ]closed|open", route_text, re.IGNORECASE)
    assert not re.search(
        r"\bpromoted\b\s*[:=]\s*true\b|\bpromotion[_ -]?true\b",
        route_text,
        re.IGNORECASE,
    )
    assert summary.get("clay_navier_stokes_promoted") is not True
    assert summary.get("clay_ns_promoted") is not True
