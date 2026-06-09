from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
CONTRACT = "ns_sprint133_universal_strategy_classifier"
SCRIPT = REPO_ROOT / "scripts" / f"{CONTRACT}.py"
OUT_DIR = REPO_ROOT / "outputs" / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_NAME = f"{CONTRACT}_rows.json"
REPORT_NAME = f"{CONTRACT}.md"

EXPECTED_STRATEGY_COUNT = 6
EXPECTED_STRATEGY_IDS = {f"strategy_{index}" for index in range(1, 7)}

CLAY_FLAG_KEYS = {
    "clay",
    "clay_promoted",
    "clay_navier_stokes_promoted",
    "full_clay_ns_solved",
    "full_clay_closure",
    "claims_full_clay_closure",
}


def run_classifier(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

    out_dir = tmp_path / CONTRACT
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
    return result, out_dir


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_rows(out_dir: Path) -> list[dict[str, Any]]:
    rows_path = out_dir / ROWS_NAME
    if rows_path.is_file():
        payload = load_json(rows_path)
        if isinstance(payload, list):
            rows = payload
        elif isinstance(payload, dict) and isinstance(payload.get("rows"), list):
            rows = payload["rows"]
        else:
            raise AssertionError(f"rows JSON has no rows list: {rows_path}")
        assert all(isinstance(row, dict) for row in rows), rows
        return rows

    csv_paths = sorted(path for path in out_dir.glob("*.csv") if "row" in path.name.lower())
    if csv_paths:
        with csv_paths[0].open(newline="", encoding="utf-8") as handle:
            return [dict(row) for row in csv.DictReader(handle)]

    raise AssertionError(f"missing rows artifact in {out_dir}")


def artifact_text(out_dir: Path, result: subprocess.CompletedProcess[str]) -> str:
    paths = sorted(
        path
        for path in out_dir.glob("*")
        if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
    )
    return "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in paths]
    )


def walk(value: Any) -> Iterable[Any]:
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        yield value
        for child in value:
            yield from walk(child)
    else:
        yield value


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = set(keys)
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if key in wanted and isinstance(value, bool):
                values.append(value)
    return values


def strategy_id(row: dict[str, Any]) -> str:
    for key in ("strategy_id", "id", "row_id", "strategy"):
        value = row.get(key)
        if isinstance(value, int):
            return f"strategy_{value}"
        if isinstance(value, str):
            match = re.search(r"(?:strategy[_ -]?)?([1-6])\b", value, re.IGNORECASE)
            if match:
                return f"strategy_{match.group(1)}"
    raise AssertionError(f"strategy row has no strategy id: {row}")


def row_text(row: dict[str, Any]) -> str:
    return json.dumps(row, sort_keys=True).lower()


def row_bool(row: dict[str, Any], *keys: str) -> bool | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            normalized = value.strip().lower()
            if normalized in {"true", "yes", "1"}:
                return True
            if normalized in {"false", "no", "0"}:
                return False
    return None


def strategy_rows_by_id(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    indexed = {strategy_id(row): row for row in rows}
    assert len(indexed) == len(rows), f"duplicate strategy ids in rows: {rows}"
    return indexed


def test_sprint133_universal_strategy_classifier_emits_summary_rows_report(
    tmp_path: Path,
) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result) if out_dir.exists() else result.stdout + result.stderr

    assert result.returncode == 0, output_text
    assert out_dir != OUT_DIR
    assert (out_dir / SUMMARY_NAME).is_file(), output_text
    assert (out_dir / ROWS_NAME).is_file(), output_text
    assert (out_dir / REPORT_NAME).is_file(), output_text
    assert (out_dir / SUMMARY_NAME).stat().st_size > 0
    assert (out_dir / ROWS_NAME).stat().st_size > 0
    assert (out_dir / REPORT_NAME).stat().st_size > 0


def test_sprint133_classifier_records_exactly_six_universal_strategies(
    tmp_path: Path,
) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    summary = load_json(out_dir / SUMMARY_NAME)
    rows = load_rows(out_dir)
    by_id = strategy_rows_by_id(rows)

    assert summary.get("strategy_count", len(rows)) == EXPECTED_STRATEGY_COUNT
    assert len(rows) == EXPECTED_STRATEGY_COUNT
    assert set(by_id) == EXPECTED_STRATEGY_IDS


def test_sprint133_classifier_keeps_all_clay_promotion_flags_false(
    tmp_path: Path,
) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    summary = load_json(out_dir / SUMMARY_NAME)
    rows = load_rows(out_dir)
    payload = {"summary": summary, "rows": rows}

    clay_flags = bool_values_for_keys(payload, *CLAY_FLAG_KEYS)
    assert clay_flags, "classifier should expose explicit Clay promotion/closure flags"
    assert all(flag is False for flag in clay_flags), output_text

    for row in rows:
        assert row_bool(row, "claims_full_clay_closure", "full_clay_closure") is not True, row
        assert row_bool(row, "clay_navier_stokes_promoted", "full_clay_ns_solved") is not True, row


def test_sprint133_strategy3_is_live_or_most_promising_unexplored(
    tmp_path: Path,
) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    row = strategy_rows_by_id(load_rows(out_dir))["strategy_3"]
    text = row_text(row)

    assert "monotone" in text or "comparison" in text, row
    assert (
        "most_promising_unexplored" in text
        or "most promising unexplored" in text
        or "live" in text
    ), row


def test_sprint133_strategy5_marks_axisymmetric_structure_theorem_live_direct(
    tmp_path: Path,
) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    row = strategy_rows_by_id(load_rows(out_dir))["strategy_5"]
    text = row_text(row)

    assert "structure" in text and "theorem" in text, row
    assert "axisymmetric" in text, row
    assert "live" in text, row
    assert "direct" in text, row


def test_sprint133_no_strategy_claims_full_clay_closure(tmp_path: Path) -> None:
    result, out_dir = run_classifier(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    rows = load_rows(out_dir)
    for row in rows:
        text = row_text(row)
        assert row_bool(row, "claims_full_clay_closure", "full_clay_closure") is not True, row
        assert "full clay closure" not in text or "no full clay closure" in text, row
        assert "clay solved" not in text, row
