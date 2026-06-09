from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint132_mechanism_exhaustion_audit.py"
STEM = "ns_sprint132_mechanism_exhaustion_audit"
DEFAULT_OUT_DIR = REPO_ROOT / "outputs" / STEM
SUMMARY_NAME = f"{STEM}_summary.json"
REPORT_NAME = f"{STEM}.md"

FAILED_ROUTES = (
    "enumeration",
    "lyapunov",
    "comparison",
    "probabilistic",
)

EXPECTED_SUMMARY_FLAGS = {
    "mechanism_exhaustion_closed": False,
    "structural_gap": True,
    "missing_calculation": False,
    "route_specific_obstruction_theorem_possible": True,
}

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_audit() -> tuple[subprocess.CompletedProcess[str], dict[str, Any], Any, str]:
    assert SCRIPT.is_file(), f"missing Sprint 132 mechanism exhaustion audit script: {SCRIPT}"

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(DEFAULT_OUT_DIR),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode in (0, 1), result.stdout + result.stderr

    json_paths = sorted(DEFAULT_OUT_DIR.glob("*.json"))
    markdown_paths = sorted(DEFAULT_OUT_DIR.glob("*.md"))
    assert json_paths, f"audit did not write JSON artifacts under {DEFAULT_OUT_DIR}"
    assert markdown_paths, f"audit did not write Markdown artifacts under {DEFAULT_OUT_DIR}"
    assert all(path.stat().st_size > 0 for path in json_paths + markdown_paths)

    summary_path = DEFAULT_OUT_DIR / SUMMARY_NAME
    if not summary_path.is_file():
        candidates = [
            path
            for path in json_paths
            if re.search(r"summary", path.name, re.IGNORECASE)
        ]
        assert candidates, f"missing summary JSON in {[path.name for path in json_paths]}"
        summary_path = candidates[0]

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    assert isinstance(summary, dict) and summary

    rows = load_rows(json_paths)
    text = "\n".join(
        [
            result.stdout,
            result.stderr,
            json.dumps(summary, sort_keys=True),
            json.dumps(rows, sort_keys=True),
            *[path.read_text(encoding="utf-8") for path in markdown_paths],
        ]
    )
    return result, summary, rows, text


def load_rows(json_paths: list[Path]) -> Any:
    row_candidates = [
        path
        for path in json_paths
        if "summary" not in path.name.lower()
        and re.search(r"(row|route|mechanism|exhaustion)", path.name, re.IGNORECASE)
    ]
    assert row_candidates, f"missing row JSON in {[path.name for path in json_paths]}"

    payload = json.loads(row_candidates[0].read_text(encoding="utf-8"))
    if isinstance(payload, list):
        assert payload and all(isinstance(row, dict) for row in payload)
        return payload
    if isinstance(payload, dict):
        rows = payload.get("rows") or payload.get("route_rows") or payload.get("failed_routes")
        assert isinstance(rows, list) and rows, f"row JSON has no nonempty rows list: {row_candidates[0].name}"
        assert all(isinstance(row, dict) for row in rows)
        return rows
    raise AssertionError(f"unexpected row JSON payload type: {type(payload).__name__}")


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def dicts_containing(value: Any, *terms: str) -> list[dict[str, Any]]:
    folded = tuple(term.lower() for term in terms)
    matches: list[dict[str, Any]] = []
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        text = json_text(item).lower()
        if all(term in text for term in folded):
            matches.append(item)
    return matches


def route_is_failed(row: dict[str, Any]) -> bool:
    if row.get("failed") is True or row.get("route_failed") is True:
        return True
    if any(
        isinstance(value, bool) and value is True and "fail" in str(key).lower()
        for key, value in row.items()
    ):
        return True
    if row.get("closed") is False or row.get("possible") is False:
        return True
    status_text = " ".join(
        str(row.get(key, ""))
        for key in ("status", "state", "result", "verdict", "decision", "obstruction")
    ).lower()
    return bool(re.search(r"\b(fail|failed|blocked|obstructed|exhausted|impossible)\b", status_text))


def clay_boolean_rows(summary: dict[str, Any]) -> list[tuple[str, bool]]:
    rows: list[tuple[str, bool]] = []
    for item in walk(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if not isinstance(value, bool):
                continue
            key_text = str(key).lower()
            if "clay" in key_text and not re.search(r"absen|not_|no_|without|forbid|detect", key_text):
                rows.append((str(key), value))
    return rows


def test_sprint132_mechanism_exhaustion_cli_writes_expected_output_surface() -> None:
    result, summary, rows, text = run_audit()

    assert DEFAULT_OUT_DIR.is_dir()
    assert (DEFAULT_OUT_DIR / SUMMARY_NAME).is_file()
    assert (DEFAULT_OUT_DIR / REPORT_NAME).is_file()
    assert rows, "audit should write nonempty route/mechanism rows"
    assert STEM in text or "mechanism exhaustion" in text.lower()
    assert result.returncode in (0, 1)
    assert isinstance(summary, dict)


def test_sprint132_summary_records_structural_gap_without_missing_calculation() -> None:
    _result, summary, _rows, _text = run_audit()

    for key, expected in EXPECTED_SUMMARY_FLAGS.items():
        assert summary.get(key) is expected, key


def test_sprint132_enumerates_four_failed_mechanism_routes() -> None:
    _result, summary, rows, text = run_audit()
    route_surface = {"summary": summary, "rows": rows}

    for route in FAILED_ROUTES:
        matches = dicts_containing(route_surface, route)
        assert matches, f"missing failed route row for {route}:\n{text}"
        assert any(route_is_failed(row) for row in matches), (
            f"route {route} is present but not recorded as failed/obstructed:\n"
            + json_text(matches)
        )


def test_sprint132_route_specific_theorem_possible_and_no_clay_flags_true() -> None:
    _result, summary, _rows, text = run_audit()

    assert summary.get("route_specific_obstruction_theorem_possible") is True
    clay_rows = clay_boolean_rows(summary)
    assert clay_rows, "summary should expose Clay boolean guard flags"
    assert all(value is False for _key, value in clay_rows), json_text(clay_rows)
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
