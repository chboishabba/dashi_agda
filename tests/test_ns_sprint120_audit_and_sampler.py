from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint120_linear_strain_anticorrelation_audit.py"
SAMPLER_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint120_polarization_sign_sampler.py"


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


def artifact_text(paths: list[Path]) -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in paths)


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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "met"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "unmet"}:
            return False
    return None


def number_at(row: dict[str, Any], *names: str) -> float | None:
    value = value_at(row, *names)
    if value is None or value == "":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


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


def rows_from_artifacts(json_payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in flatten(json_payloads):
        if isinstance(item, dict) and looks_like_sampler_row(item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def looks_like_sampler_row(row: dict[str, Any]) -> bool:
    return (
        number_at(row, "anticorrelation_product", "anticorrelationProduct") is not None
        or number_at(
            row,
            "flux",
            "signed_flux",
            "polarization_flux",
            "polarizationFlux",
            "flux_proxy",
            "fluxProxy",
        )
        is not None
        or number_at(
            row,
            "amplification",
            "amplification_rate",
            "amplificationRate",
            "amplification_proxy",
            "amplificationProxy",
        )
        is not None
    )


def test_linear_strain_anticorrelation_audit_runs_and_keeps_clay_false(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint120_linear_strain_anticorrelation_audit"
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
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False

    text = artifact_text([*json_paths, *md_paths]).lower()
    assert "true" in text
    assert "false" in text
    assert "clay" in text


def test_polarization_sign_sampler_outputs_anticorrelated_fail_closed_rows(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint120_polarization_sign_sampler"
    result = run_script(SAMPLER_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"

    payloads = load_json(json_paths)
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, "sampler did not expose sample rows"

    products = [
        number_at(row, "anticorrelation_product", "anticorrelationProduct") for row in rows
    ]
    assert all(product is not None for product in products), rows
    assert all(product <= 0 for product in products if product is not None), rows

    positive_flux_rows = [
        row
        for row in rows
        if (
            number_at(
                row,
                "flux",
                "signed_flux",
                "polarization_flux",
                "polarizationFlux",
                "flux_proxy",
                "fluxProxy",
            )
            or 0.0
        )
        > 0
    ]
    assert positive_flux_rows, rows
    assert all(
        (
            number_at(
                row,
                "amplification",
                "amplification_rate",
                "amplificationRate",
                "amplification_proxy",
                "amplificationProxy",
            )
            or 0.0
        )
        < 0
        for row in positive_flux_rows
    ), positive_flux_rows
    assert scalar_bool_for_key(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False
