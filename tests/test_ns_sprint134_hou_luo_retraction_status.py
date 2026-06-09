from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint134_hou_luo_retraction_status"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

EXPECTED_WBF_ROWS = {
    "WBF-L",
    "WBF-S",
    "WBF-MP",
    "WBF-R",
}

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_retraction_status(
    tmp_path: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, str]], str]:
    assert SCRIPT.is_file(), f"missing Worker 3 script: {SCRIPT.relative_to(REPO_ROOT)}"

    out_dir = tmp_path / STEM
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

    text = collect_artifact_text(out_dir, result)
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in json_paths + csv_paths + md_paths)

    json_payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    summary = merge_json_objects(json_payloads)
    rows_json = flatten_rows(json_payloads)
    rows_csv = load_csv_rows(csv_paths)
    assert summary, "expected at least one JSON object summary"
    assert rows_json or rows_csv, "expected JSON or CSV status rows"
    return summary, rows_json, rows_csv, text


def collect_artifact_text(out_dir: Path, result: subprocess.CompletedProcess[str]) -> str:
    paths = []
    if out_dir.exists():
        paths = sorted(
            path
            for path in out_dir.glob("*")
            if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
        )
    return "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in paths]
    )


def merge_json_objects(payloads: list[Any]) -> dict[str, Any]:
    merged: dict[str, Any] = {}
    for payload in payloads:
        if isinstance(payload, dict):
            merged.update(payload)
    return merged


def flatten_rows(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        rows: list[dict[str, Any]] = []
        for key in (
            "rows",
            "status_rows",
            "route_rows",
            "result_rows",
            "claims",
            "theorem_rows",
            "retractions",
        ):
            child = value.get(key)
            if isinstance(child, list):
                rows.extend(row for row in child if isinstance(row, dict))
        if looks_like_row(value):
            rows.append(value)
        for child in value.values():
            rows.extend(flatten_rows(child))
        return rows
    if isinstance(value, list):
        return [row for child in value for row in flatten_rows(child)]
    return []


def looks_like_row(value: dict[str, Any]) -> bool:
    if set(value) == {"key", "value"}:
        return False
    row_keys = {
        "row_id",
        "result",
        "mechanism",
        "route",
        "status",
        "classification",
        "claim",
        "theorem",
    }
    return bool(row_keys.intersection(value))


def load_csv_rows(paths: Iterable[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def artifact_json_text(*values: Any) -> str:
    return "\n".join(
        json.dumps(value, sort_keys=True, default=str)
        if not isinstance(value, str)
        else value
        for value in values
    )


def norm(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "-", str(value).lower()).strip("-")


def row_text(row: dict[str, Any]) -> str:
    return norm(artifact_json_text(row))


def row_mentions(row: dict[str, Any], *needles: str) -> bool:
    text = row_text(row)
    return all(norm(needle) in text for needle in needles)


def bool_values_for_key_fragments(payload: Any, *fragments: str) -> list[tuple[str, bool]]:
    found: list[tuple[str, bool]] = []
    wanted = tuple(fragment.lower() for fragment in fragments)
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if isinstance(value, bool) and any(fragment in str(key).lower() for fragment in wanted):
                found.append((str(key), value))
    return found


def test_sprint134_retraction_status_writes_json_csv_and_markdown(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)

    assert summary.get("contract", STEM) == STEM
    assert rows_json or rows_csv
    assert "hou" in text.lower()
    assert "luo" in text.lower()
    assert "retract" in text.lower()


def test_sprint134_retracts_axisymmetric_viscous_dominance_obstruction(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)
    all_rows = rows_json + rows_csv

    retracted_rows = [
        row
        for row in all_rows
        if row_mentions(row, "AXS", "viscous", "dominance")
        and ("retract" in row_text(row) or "withdraw" in row_text(row))
    ]
    assert retracted_rows, artifact_json_text(summary, all_rows, text)

    status_flags = bool_values_for_key_fragments(summary, "axisymmetric_hou_luo", "viscous_dominance")
    for key, value in status_flags:
        if "retract" in key.lower():
            assert value is True, (key, value)
        if "obstruct" in key.lower() and "retract" not in key.lower():
            assert value is False, (key, value)


def test_sprint134_keeps_hou_luo_axisymmetric_ns_route_open_and_live(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)
    all_rows = rows_json + rows_csv

    live_rows = [
        row
        for row in all_rows
        if row_mentions(row, "Hou", "Luo")
        and row_mentions(row, "axisymmetric")
        and ("open" in row_text(row) or "live" in row_text(row))
    ]
    assert live_rows, artifact_json_text(summary, all_rows, text)

    text_norm = norm(text)
    assert "hou-luo-axisymmetric-ns-route" in text_norm or (
        "hou-luo" in text_norm and "open" in text_norm and "live" in text_norm
    )


def test_sprint134_wbf_exact_rows_remain_intact(tmp_path: Path) -> None:
    _summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)
    all_rows = rows_json + rows_csv

    seen_exact: set[str] = set()
    for label in EXPECTED_WBF_ROWS:
        matching = [
            row
            for row in all_rows
            if label.lower() in artifact_json_text(row).lower()
            and "exact" in row_text(row)
            and "intact" in row_text(row)
        ]
        assert matching, f"missing intact exact row for {label}\n{text}"
        seen_exact.add(label)

    assert seen_exact == EXPECTED_WBF_ROWS


def test_sprint134_records_source_log_gronwall_inversion(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)
    all_rows = rows_json + rows_csv
    joined = artifact_json_text(summary, all_rows, text).lower()

    assert "log" in joined
    assert "gronwall" in joined
    assert "source" in joined
    assert "viscos" in joined
    assert "super" in joined and "exponential" in joined
    assert (
        "dominates" in joined
        or "beats" in joined
        or "may beat" in joined
        or "wrong way" in joined
        or "overpower" in joined
    )
    assert "tau" in joined or "τ" in joined


def test_sprint134_makes_no_full_clay_claim_and_keeps_clay_flags_false(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_retraction_status(tmp_path)
    payload = [summary, rows_json, rows_csv]

    clay_flags = bool_values_for_key_fragments(payload, "clay")
    assert clay_flags, "expected explicit Clay guard flags"
    for key, value in clay_flags:
        if key.lower() in {"clay_absent", "clay_not_promoted", "no_clay_promotion_detected"}:
            continue
        assert value is False, f"Clay flag must remain false: {(key, value)}"

    full_clay_flags = [
        value
        for key, value in clay_flags
        if "full" in key.lower() and "clay" in key.lower()
    ]
    assert full_clay_flags and all(value is False for value in full_clay_flags)

    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
