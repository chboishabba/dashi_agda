from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint118_geometric_correlation_audit.py"
SAMPLER_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint118_alignment_sign_sampler.py"


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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "positive"}:
            return True
        if lowered in {
            "false",
            "0",
            "no",
            "fail",
            "failed",
            "open",
            "blocked",
            "non-positive",
            "nonpositive",
        }:
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
    return dedupe_rows(rows)


def looks_like_sampler_row(row: dict[str, Any]) -> bool:
    return (
        value_at(row, "regime", "case", "profile", "alignment_type") is not None
        or number_at(row, "flux", "signed_flux", "alignment_flux") is not None
        or boolish(value_at(row, "compressive", "is_compressive")) is not None
        or value_at(row, "sign_class", "flux_sign") is not None
    )


def dedupe_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: dict[tuple[str, str, float | None], dict[str, Any]] = {}
    for row in rows:
        label = str(
            value_at(row, "case", "case_id", "regime", "profile", "alignment_type") or ""
        )
        sign_class = str(value_at(row, "sign_class", "flux_sign", "classification") or "")
        flux = number_at(row, "flux", "signed_flux", "alignment_flux")
        deduped.setdefault((label, sign_class, flux), row)
    return list(deduped.values())


def row_is_compressive(row: dict[str, Any]) -> bool:
    explicit = boolish(value_at(row, "compressive", "is_compressive"))
    if explicit is not None:
        return explicit
    text = json.dumps(row, sort_keys=True).lower()
    return "compressive" in text and "extensive" not in text


def row_is_extensive(row: dict[str, Any]) -> bool:
    explicit = boolish(value_at(row, "extensive", "is_extensive"))
    if explicit is not None:
        return explicit
    text = json.dumps(row, sort_keys=True).lower()
    return "extensive" in text


def row_has_positive_flux(row: dict[str, Any]) -> bool:
    flux = number_at(row, "flux", "signed_flux", "alignment_flux")
    if flux is not None:
        return flux > 0
    text = json.dumps(row, sort_keys=True).lower()
    return "positive" in text and "non-positive" not in text and "nonpositive" not in text


def row_has_non_positive_flux(row: dict[str, Any]) -> bool:
    flux = number_at(row, "flux", "signed_flux", "alignment_flux")
    if flux is not None:
        return flux <= 0
    text = json.dumps(row, sort_keys=True).lower()
    return "non-positive" in text or "nonpositive" in text or "zero" in text or "negative" in text


def test_geometric_correlation_audit_runs_and_keeps_clay_false(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint118_geometric_correlation_audit"
    result = run_script(AUDIT_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths, artifact_text = read_artifacts(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert not csv_paths, "geometric correlation audit should not need CSV output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    boolean_fields = all_boolean_fields(payloads)
    assert any(boolean_fields.values()), boolean_fields
    assert any(value is False for value in boolean_fields.values()), boolean_fields
    assert scalar_bool_for_key(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False
    assert "true" in artifact_text.lower()
    assert "false" in artifact_text.lower()
    assert "clay" in artifact_text.lower()


def test_alignment_sign_sampler_outputs_flux_rows_and_fail_closed_summary(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint118_alignment_sign_sampler"
    result = run_script(SAMPLER_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths, artifact_text = read_artifacts(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, "sampler did not expose sample rows"
    assert any(row_is_compressive(row) and row_has_positive_flux(row) for row in rows), rows
    assert any(row_is_extensive(row) and row_has_non_positive_flux(row) for row in rows), rows

    assert scalar_bool_for_key(
        payloads,
        "persistent_alignment_existence_closed",
        "persistentAlignmentExistenceClosed",
    ) is False
    assert scalar_bool_for_key(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay",
    ) is False
    assert "persistent_alignment_existence_closed" in artifact_text
    assert "clay" in artifact_text.lower()
