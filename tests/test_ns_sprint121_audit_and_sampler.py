from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint121_rotating_strain_audit.py"
SAMPLER_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint121_rotating_phase_lag_sampler.py"


def run_script(script: Path, out_dir: Path) -> subprocess.CompletedProcess[str]:
    assert script.exists(), f"required script is missing: {script}"
    return subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in paths]


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalize_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def value_at(row: dict[str, Any], *names: str) -> Any:
    normalized_names = {normalize_key(name) for name in names}
    for key, value in row.items():
        if normalize_key(str(key)) in normalized_names:
            return value
    return None


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "closed", "met", "favorable"}:
            return True
        if lowered in {"false", "0", "no", "open", "blocked", "unmet", "unfavorable"}:
            return False
    return None


def intish(value: Any) -> int | None:
    if value is None or value == "":
        return None
    try:
        as_float = float(value)
    except (TypeError, ValueError):
        return None
    if as_float.is_integer():
        return int(as_float)
    return None


def scalar_bool_for_key(payloads: list[Any], *names: str) -> bool:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[bool] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) not in normalized_names:
                continue
            if isinstance(value, (dict, list)):
                continue
            parsed = boolish(value)
            if parsed is not None:
                matches.append(parsed)
    assert matches, f"missing scalar boolean-like field for {names}"
    return matches[-1]


def scalar_int_for_key(payloads: list[Any], *names: str) -> int:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[int] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in normalized_names:
                parsed = intish(value)
                if parsed is not None:
                    matches.append(parsed)
    assert matches, f"missing scalar integer-like field for {names}"
    return matches[-1]


def boolean_values(payloads: list[Any]) -> list[bool]:
    values: list[bool] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for value in item.values():
            if isinstance(value, (dict, list)):
                continue
            parsed = boolish(value)
            if parsed is not None:
                values.append(parsed)
    return values


def rows_from_artifacts(json_payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in flatten(json_payloads):
        if isinstance(item, dict) and looks_like_sampler_row(item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return dedupe_rows(rows)


def dedupe_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: dict[tuple[Any, ...], dict[str, Any]] = {}
    for row in rows:
        key = (
            value_at(row, "case", "case_id", "row_id"),
            comparable_value(value_at(row, "omega")),
            comparable_value(value_at(row, "tau")),
            comparable_value(value_at(row, "phase_lag", "phaseLag")),
            value_at(row, "classification"),
        )
        if all(value is None for value in key):
            key = (json.dumps(row, sort_keys=True),)
        deduped.setdefault(key, row)
    return list(deduped.values())


def comparable_value(value: Any) -> Any:
    if value is None:
        return None
    try:
        return round(float(value), 12)
    except (TypeError, ValueError):
        return str(value)


def looks_like_sampler_row(row: dict[str, Any]) -> bool:
    return (
        value_at(row, "case", "case_id", "row_id", "phase_lag", "phaseLag") is not None
        or favorable_by_row_booleans(row) is not None
    )


def favorable_by_row_booleans(row: dict[str, Any]) -> bool | None:
    explicit = boolish(
        value_at(
            row,
            "favorable",
            "is_favorable",
            "favorable_row",
            "favorableRow",
            "favorable_case",
            "favorableCase",
        )
    )
    if explicit is not None:
        return explicit

    boolean_terms = {
        "phase_lag_favorable",
        "phaseLagFavorable",
        "rotating_strain_favorable",
        "rotatingStrainFavorable",
        "strain_orientation_favorable",
        "strainOrientationFavorable",
        "lag_window_favorable",
        "lagWindowFavorable",
    }
    values = [
        parsed
        for name in boolean_terms
        if (parsed := boolish(value_at(row, name))) is not None
    ]
    if values:
        return all(values)
    return None


def test_rotating_strain_audit_runs_and_records_coherent_false_claims(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint121_rotating_strain_audit"
    result = run_script(AUDIT_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert not csv_paths, "audit should not need CSV output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json(json_paths)
    values = boolean_values(payloads)
    assert values, "audit did not expose boolean-like fields"
    assert any(values), values
    assert any(value is False for value in values), values
    assert scalar_bool_for_key(
        payloads,
        "fail_closed",
        "failClosed",
    ) is True
    assert scalar_bool_for_key(
        payloads,
        "proof_claimed",
        "proofClaimed",
    ) is False
    assert scalar_bool_for_key(payloads, "promotion_hold", "promotionHold") is True
    assert scalar_bool_for_key(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False


def test_rotating_phase_lag_sampler_counts_favorable_rows_and_keeps_claims_false(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint121_rotating_phase_lag_sampler"
    result = run_script(SAMPLER_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"

    payloads = load_json(json_paths)
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, "sampler did not expose sample rows"

    favorable_flags = [favorable_by_row_booleans(row) for row in rows]
    assert all(flag is not None for flag in favorable_flags), rows
    favorable_count = sum(1 for flag in favorable_flags if flag is True)
    assert scalar_int_for_key(
        payloads,
        "favorable_row_count",
        "favorableRowCount",
    ) == favorable_count

    assert scalar_bool_for_key(
        payloads,
        "non_circular_persistence_established",
        "nonCircularPersistenceEstablished",
    ) is False
    assert scalar_bool_for_key(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False
