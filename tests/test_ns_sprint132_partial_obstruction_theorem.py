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
CONTRACT = "ns_sprint132_partial_obstruction_theorem"
SCRIPT = REPO_ROOT / "scripts" / f"{CONTRACT}.py"
DEFAULT_OUT_DIR = REPO_ROOT / "outputs" / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_NAME = f"{CONTRACT}_rows.json"
REPORT_NAME = f"{CONTRACT}.md"

EXPECTED_THEOREM = "NSPartialRegularityFromObstructionTower"
EXPECTED_EXACT_ROUTES = {"WBF-L", "WBF-S", "WBF-MP", "WBF-R"}
EXPECTED_CONDITIONAL_ROUTES = {"WBF-V", "AXS"}
EXPECTED_ROUTES = EXPECTED_EXACT_ROUTES | EXPECTED_CONDITIONAL_ROUTES
EXPECTED_SCOPE = "analyzed_route_classes_only"


def run_theorem_script(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path]:
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


def run_theorem_script_default_output() -> subprocess.CompletedProcess[str]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

    return subprocess.run(
        [sys.executable, str(SCRIPT), "--repo-root", str(REPO_ROOT)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_rows_from_json(path: Path) -> list[dict[str, Any]]:
    payload = load_json(path)
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict) and isinstance(payload.get("rows"), list):
        rows = payload["rows"]
    else:
        raise AssertionError(f"rows JSON must be a list or contain a rows list: {path}")
    assert all(isinstance(row, dict) for row in rows), f"non-object row in {path}"
    return rows


def load_rows(out_dir: Path) -> list[dict[str, Any]]:
    rows_path = out_dir / ROWS_NAME
    if rows_path.is_file():
        return load_rows_from_json(rows_path)

    row_json_paths = sorted(path for path in out_dir.glob("*.json") if "row" in path.name.lower())
    if row_json_paths:
        return load_rows_from_json(row_json_paths[0])

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


def json_values(payload: Any) -> Iterable[Any]:
    if isinstance(payload, dict):
        yield payload
        for value in payload.values():
            yield from json_values(value)
    elif isinstance(payload, list):
        for value in payload:
            yield from json_values(value)
    else:
        yield payload


def normalize_status(value: Any) -> str:
    return str(value).strip().lower().replace("-", "_").replace(" ", "_")


def row_theorem(row: dict[str, Any]) -> str:
    value = row.get("theorem", row.get("theorem_id", row.get("theorem_name")))
    assert isinstance(value, str) and value, f"row missing theorem field: {row}"
    return value


def row_scope(row: dict[str, Any]) -> str:
    value = row.get("scope", row.get("theorem_scope"))
    assert isinstance(value, str) and value, f"row missing scope/theorem_scope field: {row}"
    return value


def row_route(row: dict[str, Any]) -> str:
    value = row.get("route_class", row.get("row_id"))
    assert isinstance(value, str) and value, f"row missing route_class/row_id field: {row}"
    return value


def rows_by_route(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    indexed = {row_route(row): row for row in rows}
    assert len(indexed) == len(rows), f"duplicate route rows: {rows}"
    return indexed


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = set(keys)
    values: list[bool] = []
    for item in json_values(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if key in wanted and isinstance(value, bool):
                values.append(value)
    return values


def test_sprint132_partial_obstruction_script_exists() -> None:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))


def test_sprint132_cli_writes_summary_rows_report_to_requested_output(
    tmp_path: Path,
) -> None:
    result, out_dir = run_theorem_script(tmp_path)
    output_text = artifact_text(out_dir, result) if out_dir.exists() else result.stdout + result.stderr

    assert result.returncode == 0, output_text
    assert out_dir != DEFAULT_OUT_DIR
    assert (out_dir / SUMMARY_NAME).is_file(), output_text
    assert (out_dir / ROWS_NAME).is_file(), output_text
    assert (out_dir / REPORT_NAME).is_file(), output_text
    assert (out_dir / SUMMARY_NAME).stat().st_size > 0
    assert (out_dir / ROWS_NAME).stat().st_size > 0
    assert (out_dir / REPORT_NAME).stat().st_size > 0


def test_sprint132_default_cli_inspects_canonical_output_directory() -> None:
    result = run_theorem_script_default_output()
    output_text = (
        artifact_text(DEFAULT_OUT_DIR, result)
        if DEFAULT_OUT_DIR.exists()
        else result.stdout + result.stderr
    )

    assert result.returncode == 0, output_text
    assert DEFAULT_OUT_DIR.is_dir(), output_text
    assert (DEFAULT_OUT_DIR / SUMMARY_NAME).is_file(), output_text
    assert (DEFAULT_OUT_DIR / ROWS_NAME).is_file(), output_text
    assert (DEFAULT_OUT_DIR / REPORT_NAME).is_file(), output_text

    summary = load_json(DEFAULT_OUT_DIR / SUMMARY_NAME)
    rows = load_rows(DEFAULT_OUT_DIR)
    assert summary["row_count"] == 6
    assert len(rows) == 6


def test_sprint132_rows_have_six_theorem_scope_status_records(tmp_path: Path) -> None:
    result, out_dir = run_theorem_script(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    rows = load_rows(out_dir)
    assert len(rows) == 6, rows
    for row in rows:
        assert isinstance(row.get("theorem"), str) and row["theorem"], row
        assert row_theorem(row) == EXPECTED_THEOREM
        assert row_scope(row) == EXPECTED_SCOPE
        assert isinstance(row.get("status"), str) and row["status"], row

    assert set(rows_by_route(rows)) == EXPECTED_ROUTES


def test_sprint132_exact_and_conditional_route_rows_are_separated(
    tmp_path: Path,
) -> None:
    result, out_dir = run_theorem_script(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    rows = load_rows(out_dir)
    by_route = rows_by_route(rows)
    exact = {
        route
        for route, row in by_route.items()
        if normalize_status(row["status"]) == "exact"
    }
    conditional = {
        route
        for route, row in by_route.items()
        if normalize_status(row["status"]) == "conditional_on"
    }

    assert exact == EXPECTED_EXACT_ROUTES
    assert conditional == EXPECTED_CONDITIONAL_ROUTES

    summary = load_json(out_dir / SUMMARY_NAME)
    assert set(summary["exact_routes"]) == EXPECTED_EXACT_ROUTES
    assert set(summary["conditional_routes"]) == EXPECTED_CONDITIONAL_ROUTES
    assert summary["exact_row_count"] == 4
    assert summary["conditional_row_count"] == 2


def test_sprint132_axs_row_records_no_log_biot_savart_dependency(tmp_path: Path) -> None:
    result, out_dir = run_theorem_script(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    rows = load_rows(out_dir)
    axs_rows = [
        row
        for row in rows
        if row_route(row) == "AXS"
        or str(row.get("class_family", "")).upper() == "CLASS_AXS"
    ]
    assert axs_rows, rows
    axs_text = json.dumps(axs_rows, sort_keys=True)
    assert "NoLogAxisymmetricBiotSavartUniform" in axs_text
    assert axs_rows[0]["condition"] == "NoLogAxisymmetricBiotSavartUniform"


def test_sprint132_summary_keeps_full_clay_and_promotion_false(tmp_path: Path) -> None:
    result, out_dir = run_theorem_script(tmp_path)
    output_text = artifact_text(out_dir, result)
    assert result.returncode == 0, output_text

    summary = load_json(out_dir / SUMMARY_NAME)
    rows = load_rows(out_dir)
    assert summary["full_clay_ns_solved"] is False
    assert summary["clay_navier_stokes_promoted"] is False

    values = bool_values_for_keys(
        [summary, rows],
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    assert values and not any(values), output_text
    assert not re.search(
        r'"(?:full_clay_ns_solved|clay_navier_stokes_promoted)"\s*:\s*true',
        output_text,
        re.IGNORECASE,
    )
