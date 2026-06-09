from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint96_collapse_scaling_sanity.py"
OUT_STEM = "ns_sprint96_collapse_scaling_sanity"

REQUIRED_GATES = (
    ("finite", "time", "collapse"),
    ("leray", "energy", "compatible"),
    ("conditional", "lower", "bound"),
    ("singularity", "extraction"),
    ("no", "forbidden", "dependency"),
)


def run_sanity(tmp_path: Path) -> tuple[Path, dict[str, Any], str]:
    assert SCRIPT.exists(), "Sprint96 collapse scaling sanity script is missing"

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
    assert json_paths, "sanity script did not write JSON output"
    assert md_paths, "sanity script did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *md_paths]:
        parts.append(path.read_text(encoding="utf-8"))
    return out_dir, summary, "\n".join(parts)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalized(value: object) -> str:
    return str(value).strip().replace("_", "-").lower()


def boolish(value: object) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        if value == 1:
            return True
        if value == 0:
            return False
    if isinstance(value, str):
        lowered = normalized(value)
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "accepted", "promoted"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "fail",
            "failed",
            "open",
            "blocked",
            "rejected",
            "not-promoted",
            "fail-closed",
            "hold",
        }:
            return False
    return None


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


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    return [
        parsed
        for parsed in (boolish(value) for value in values_for_key_terms(payload, *terms))
        if parsed is not None
    ]


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def candidate_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for key in ("candidates", "candidate_sources", "rows", "source_rows"):
        value = summary.get(key)
        if isinstance(value, list):
            rows.extend(row for row in value if isinstance(row, dict))
    return rows


def test_ns_sprint96_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, text = run_sanity(tmp_path)

    assert summary.get("contract", OUT_STEM) == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*96|sprint96", text, re.IGNORECASE)
    assert re.search(r"collapse", text, re.IGNORECASE)
    assert re.search(r"scaling", text, re.IGNORECASE)


def test_ns_sprint96_fails_closed_with_zero_accepted_sources(tmp_path: Path) -> None:
    _out_dir, summary, text = run_sanity(tmp_path)

    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert summary.get("fail_closed") is True
    assert str(summary.get("route_decision", "")).upper() == "FAIL_CLOSED"
    assert str(summary.get("final_decision", "")).upper() == "FAIL_CLOSED"
    assert "FAIL_CLOSED" in text


def test_ns_sprint96_lists_required_gates(tmp_path: Path) -> None:
    _out_dir, summary, text = run_sanity(tmp_path)
    combined_text = json.dumps(summary, sort_keys=True) + "\n" + text

    gates = values_for_key_terms(summary, "required", "gate")
    assert gates, "summary should expose required gates"
    for terms in REQUIRED_GATES:
        assert re.search(
            r"[\w *-]{0,80}".join(re.escape(term) for term in terms),
            combined_text,
            re.IGNORECASE,
        ), terms


def test_ns_sprint96_rejects_candidates_with_reasons(tmp_path: Path) -> None:
    _out_dir, summary, text = run_sanity(tmp_path)

    rows = candidate_rows(summary)
    assert rows, "summary should list candidate sources"
    for row in rows:
        assert boolish(row.get("accepted")) is not True, row
        reason_values = [
            value
            for key, value in row.items()
            if re.search(r"reason|note|rejection|blocked|failure", key, re.IGNORECASE)
        ]
        assert any(str(value).strip() for value in reason_values), row

    assert re.search(r"reject|rejected|blocked|fail", text, re.IGNORECASE)
    assert re.search(r"reason|because|lacks|missing|does not", text, re.IGNORECASE)


def test_ns_sprint96_does_not_promote_clay(tmp_path: Path) -> None:
    _out_dir, summary, text = run_sanity(tmp_path)

    clay_values = bool_values_for_key_terms(summary, "clay")
    assert clay_values, "sanity output should expose Clay promotion state"
    assert not any(clay_values), clay_values
    assert re.search(r"clay", text, re.IGNORECASE)
    assert not re.search(
        r"clay[\w -]{0,80}[:=]\s*(true|1|yes|closed|promoted|accepted)\b",
        text,
        re.IGNORECASE,
    )
