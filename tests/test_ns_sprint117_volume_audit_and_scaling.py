from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint117_general_volume_suppression_audit.py"
SCALING_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint117_swirl_volume_scaling.py"


def run_script(script: Path, out_dir: Path) -> subprocess.CompletedProcess[str]:
    assert script.exists(), f"required script is missing: {script}"
    return subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def read_artifacts(out_dir: Path) -> tuple[list[Path], list[Path], list[Path], str]:
    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    text = "\n".join(
        path.read_text(encoding="utf-8") for path in [*json_paths, *csv_paths, *md_paths]
    )
    return json_paths, csv_paths, md_paths, text


def load_json_artifacts(paths: list[Path]) -> list[Any]:
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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "rejected"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "accepted"}:
            return False
    return None


def bool_for_key(payloads: list[Any], *names: str) -> bool:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[bool] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in normalized_names:
                parsed = boolish(value)
                if parsed is not None:
                    matches.append(parsed)
    assert matches, f"missing boolean-like field for {names}"
    return matches[-1]


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


def all_boolean_fields(payloads: list[Any]) -> dict[str, bool]:
    fields: dict[str, bool] = {}
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            parsed = boolish(value)
            if parsed is not None:
                fields[str(key)] = parsed
    return fields


def number_at(row: dict[str, Any], *names: str) -> float | None:
    value = value_at(row, *names)
    if value is None or value == "":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def rows_from_artifacts(json_payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in flatten(json_payloads):
        if isinstance(item, dict) and (
            number_at(item, "r_H", "rH", "horizon_radius") is not None
            or number_at(item, "alpha") is not None
        ):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return dedupe_rows(rows)


def dedupe_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: dict[tuple[str, float | None, float | None], dict[str, Any]] = {}
    for row in rows:
        profile = str(value_at(row, "profile") or "")
        alpha = number_at(row, "alpha")
        r_h = number_at(row, "r_H", "rH", "horizon_radius")
        deduped.setdefault((profile, alpha, r_h), row)
    return list(deduped.values())


def row_bool(row: dict[str, Any], *names: str) -> bool | None:
    value = value_at(row, *names)
    return boolish(value)


def finite_energy_ratio(row: dict[str, Any]) -> float | None:
    return number_at(
        row,
        "finite_energy_ratio",
        "finite_energy_volume_ratio",
        "volume_ratio",
        "energy_ratio",
        "ratio",
    )


def row_rejected(row: dict[str, Any]) -> bool:
    explicit = row_bool(row, "rejected", "is_rejected")
    if explicit is not None:
        return explicit
    accepted = row_bool(row, "accepted", "is_accepted")
    if accepted is not None:
        return not accepted
    decision = value_at(row, "decision", "status")
    return isinstance(decision, str) and "reject" in decision.lower()


def summary_payload(payloads: list[Any], contract: str) -> dict[str, Any]:
    for payload in payloads:
        if isinstance(payload, dict) and payload.get("contract") == contract:
            return payload
    for payload in payloads:
        if isinstance(payload, dict):
            return payload
    raise AssertionError("missing summary JSON object")


def test_general_volume_suppression_audit_runs_and_exposes_true_false_flags(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint117_general_volume_suppression_audit"
    result = run_script(AUDIT_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, _csv_paths, md_paths, artifact_text = read_artifacts(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    boolean_fields = all_boolean_fields(payloads)
    assert any(boolean_fields.values()), boolean_fields
    assert any(value is False for value in boolean_fields.values()), boolean_fields
    summary = summary_payload(payloads, "ns_sprint117_general_volume_suppression_audit")
    assert boolish(summary.get("clay_navier_stokes_promoted")) is False
    if "assigned_bools" in summary:
        assert boolish(summary["assigned_bools"].get("clayNavierStokesPromoted")) is False
    assert "true" in artifact_text.lower()
    assert "false" in artifact_text.lower()


def test_swirl_volume_scaling_outputs_monotone_rows_and_rejects_singular_cases(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint117_swirl_volume_scaling"
    result = run_script(SCALING_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths, _artifact_text = read_artifacts(out_dir)
    assert json_paths, "scaling did not write JSON output"
    assert csv_paths, "scaling did not write CSV output"
    assert md_paths, "scaling did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    rows = rows_from_artifacts(payloads, csv_paths)
    finite_rows = [
        row
        for row in rows
        if row_bool(row, "finite_energy", "finiteEnergy") is True
        and finite_energy_ratio(row) is not None
        and number_at(row, "alpha") is not None
        and number_at(row, "r_H", "rH", "horizon_radius") is not None
    ]
    assert finite_rows, "missing finite-energy scaling rows"

    rows_by_alpha: dict[float, list[dict[str, Any]]] = {}
    for row in finite_rows:
        alpha = number_at(row, "alpha")
        assert alpha is not None
        rows_by_alpha.setdefault(alpha, []).append(row)
    assert rows_by_alpha

    for alpha, alpha_rows in rows_by_alpha.items():
        ordered = sorted(
            alpha_rows,
            key=lambda row: number_at(row, "r_H", "rH", "horizon_radius") or math.nan,
            reverse=True,
        )
        ratios = [finite_energy_ratio(row) for row in ordered]
        assert all(ratio is not None and math.isfinite(ratio) for ratio in ratios), alpha
        assert all(left > right for left, right in zip(ratios, ratios[1:])), (alpha, ratios)

    singular_rows = [
        row
        for row in rows
        if row_bool(row, "finite_energy", "finiteEnergy") is False
        or row_bool(row, "singular", "is_singular") is True
    ]
    assert singular_rows, "missing singular/rejected rows"
    for row in singular_rows:
        assert row_bool(row, "finite_energy", "finiteEnergy") is False, row
        assert row_rejected(row) is True, row

    summary = summary_payload(payloads, "ns_sprint117_swirl_volume_scaling")
    assert boolish(summary.get("clay")) is False
    assert boolish(summary.get("clay_promoted")) is False
    assert boolish(summary.get("clay_navier_stokes_promoted")) is False
