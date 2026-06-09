from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint114_reconnection_window_classifier.py"
OUT_STEM = "ns_sprint114_reconnection_window_classifier"


def run_classifier(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint114 reconnection window classifier script is missing"

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
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths = sorted(out_dir.glob("*.json"))
    md_paths = sorted(out_dir.glob("*.md"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    assert json_paths, "classifier did not write JSON output"
    assert md_paths, "classifier did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    rows: list[dict[str, Any]] = []
    if isinstance(summary.get("rows"), list):
        rows.extend(row for row in summary["rows"] if isinstance(row, dict))

    for path in json_paths:
        if path == summary_path:
            continue
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            rows.extend(row for row in payload if isinstance(row, dict))
        elif isinstance(payload, dict) and isinstance(payload.get("rows"), list):
            rows.extend(row for row in payload["rows"] if isinstance(row, dict))
        elif isinstance(payload, dict):
            for key, value in payload.items():
                if isinstance(value, list):
                    rows.extend(
                        {"_json_name": path.name, "_row_group": key, **row}
                        for row in value
                        if isinstance(row, dict)
                    )

    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))

    parts = [json.dumps(summary, sort_keys=True), result.stdout, result.stderr]
    for path in [*json_paths, *csv_paths, *md_paths]:
        parts.append(path.read_text(encoding="utf-8"))
    return out_dir, summary, rows, "\n".join(parts)


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
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "rejected"}:
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


def numeric_summary_value(summary: dict[str, Any], *terms: str) -> int:
    values = values_for_key_terms(summary, *terms)
    assert values, f"missing summary count key containing terms: {terms}"
    for value in values:
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.strip().isdigit():
            return int(value.strip())
    raise AssertionError({"terms": terms, "values": values})


def candidate_name(candidate: dict[str, Any], fallback: int) -> str:
    for key in ("family", "candidate_family", "name", "candidate", "source_family", "family_id"):
        value = candidate.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return f"candidate-{fallback}"


def unique_candidate_rows(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    candidates = summary.get("rows") if isinstance(summary.get("rows"), list) else []
    merged = [row for row in candidates if isinstance(row, dict)]
    merged.extend(row for row in rows if row not in merged)

    unique: dict[str, dict[str, Any]] = {}
    for index, candidate in enumerate(merged):
        unique.setdefault(candidate_name(candidate, index), candidate)
    return list(unique.values())


def sequence_value(candidate: dict[str, Any], key: str) -> list[str]:
    value = candidate.get(key)
    if isinstance(value, list):
        return [str(item) for item in value if str(item).strip()]
    if isinstance(value, tuple):
        return [str(item) for item in value if str(item).strip()]
    if isinstance(value, str):
        lowered = normalized(value)
        if lowered in {"", "none", "[]"}:
            return []
        return [part.strip() for part in re.split(r"[;,]", value) if part.strip()]
    return []


def test_ns_sprint114_exits_one_and_writes_json_markdown(tmp_path: Path) -> None:
    out_dir, summary, _rows, text = run_classifier(tmp_path)

    assert summary.get("contract") == OUT_STEM
    assert sorted(out_dir.glob("*.json"))
    assert sorted(out_dir.glob("*.md"))
    assert re.search(r"sprint\s*114|sprint114", text, re.IGNORECASE)
    assert re.search(r"reconnection", text, re.IGNORECASE)
    assert re.search(r"window", text, re.IGNORECASE)
    assert re.search(r"classif", text, re.IGNORECASE)


def test_ns_sprint114_zero_accepted_sources_keeps_incomplete_and_unpromoted(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    combined = {"summary": summary, "rows": rows}

    assert summary.get("complete") is False
    assert summary.get("clay_navier_stokes_promoted") is False
    assert numeric_summary_value(summary, "accepted", "source", "count") == 0
    assert not any(boolish(value) for value in values_for_key_terms(combined, "clay"))
    assert re.search(r"accepted[-_ ]source[-_ ]count|accepted source count", text, re.IGNORECASE)
    assert re.search(r"`?0`?", text)


def test_ns_sprint114_lists_partial_supporting_thin_core_and_elliptic_candidates(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = unique_candidate_rows(summary, rows)
    candidate_texts = [json.dumps(candidate, sort_keys=True) for candidate in candidates]

    assert candidates
    assert any(
        re.search(r"thin[-_\s]*core.*correction|correction.*thin[-_\s]*core", candidate_text, re.IGNORECASE)
        and re.search(r"partial|support", candidate_text, re.IGNORECASE)
        for candidate_text in candidate_texts
    ), candidate_texts
    assert any(
        re.search(r"elliptic[-_\s]*backreaction|backreaction.*elliptic", candidate_text, re.IGNORECASE)
        and re.search(r"partial|support", candidate_text, re.IGNORECASE)
        for candidate_text in candidate_texts
    ), candidate_texts
    assert re.search(r"thin[-_\s]*core.*correction|correction.*thin[-_\s]*core", text, re.IGNORECASE)
    assert re.search(r"elliptic[-_\s]*backreaction|backreaction.*elliptic", text, re.IGNORECASE)


def test_ns_sprint114_reconnection_window_lower_bound_gate_remains_open(
    tmp_path: Path,
) -> None:
    _out_dir, summary, rows, text = run_classifier(tmp_path)
    candidates = unique_candidate_rows(summary, rows)
    required_gates = summary.get("required_gates")

    assert isinstance(required_gates, list) and "reconnection_window_lower_bound" in required_gates

    for candidate in candidates:
        gate_results = candidate.get("gate_results")
        assert isinstance(gate_results, dict), candidate
        assert "reconnection_window_lower_bound" in gate_results, candidate
        assert boolish(gate_results["reconnection_window_lower_bound"]) is not True, candidate
        assert "reconnection_window_lower_bound" in sequence_value(candidate, "failed_gates")
        assert boolish(candidate.get("accepted")) is not True

    combined_text = json.dumps({"summary": summary, "rows": rows}, sort_keys=True) + "\n" + text
    assert "reconnection-window-lower-bound" in normalized(combined_text)
