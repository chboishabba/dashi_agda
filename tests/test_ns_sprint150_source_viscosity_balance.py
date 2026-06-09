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
STEM = "ns_sprint150_source_viscosity_balance"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
AGDA_MODULE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint150SourceViscosityBalanceReceipt.agda"
)

REQUIRED_ROW_IDS = {
    "source_integral_lower_bound",
    "retained_viscosity_lower_bound",
    "off_axis_gain_absorption",
    "log_feedback_absorption",
    "cutoff_localization_error",
    "boundary_annular_budget",
    "nonlocal_tail_control",
    "large_data_uniformity",
    "localized_source_beats_viscosity",
    "clay_guard",
}

FALSE_FLAGS = {
    "source_integral_lower_bound_proved",
    "retained_viscosity_lower_bound_proved",
    "source_beats_retained_viscosity",
    "localized_source_viscosity_balance_proved",
    "migration_initiation_threshold_promoted",
    "scaling_consistency_promoted",
    "symmetric_hou_luo_bkm_finite",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
}

TRUE_CLOSURE_PATTERNS = tuple(
    re.compile(rf'"{name}"\s*:\s*true\b', re.IGNORECASE)
    for name in FALSE_FLAGS
)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in walk(payloads):
        if isinstance(item, dict) and "row_id" in item:
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(payloads: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted and isinstance(value, bool):
                values.append(value)
    return values


def run_ledger(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
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
    paths = sorted(out_dir.glob("*")) if out_dir.exists() else []
    json_paths = [path for path in paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in paths if path.suffix.lower() == ".md"]
    text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])
    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, text
    return payloads, rows, text, out_dir


def row_by_id(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    by_id: dict[str, dict[str, Any]] = {}
    for row in rows:
        row_id = row.get("row_id")
        if isinstance(row_id, str) and row_id in REQUIRED_ROW_IDS:
            by_id.setdefault(row_id, row)
    return by_id


def test_source_viscosity_balance_ledger_rows_and_fail_closed_flags(tmp_path: Path) -> None:
    payloads, rows, text, out_dir = run_ledger(tmp_path)
    by_id = row_by_id(rows)

    assert out_dir.name == STEM
    assert set(by_id) == REQUIRED_ROW_IDS
    assert "LocalizedSourceViscosityBalanceAtMigratingMaximum" in text
    assert "SourceIntegralLowerBoundForMigratingMaximum" in text
    assert "RetainedViscosityLowerBoundAtMigratingMaximum" in text
    assert "OffAxisGainAbsorptionLemma" in text
    assert "LogFeedbackAbsorptionLemma" in text

    artifact_complete = bool_values_for_keys(payloads, "artifact_complete")
    invariant_valid = bool_values_for_keys(payloads, "invariant_valid")
    assert artifact_complete and all(artifact_complete)
    assert invariant_valid and all(invariant_valid)

    for name in FALSE_FLAGS:
        values = bool_values_for_keys(payloads, name)
        assert values, f"missing false flag {name}\n{text}"
        assert all(value is False for value in values), (name, values)
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_source_viscosity_balance_records_exact_deficits_and_blockers(tmp_path: Path) -> None:
    payloads, rows, text, _out_dir = run_ledger(tmp_path)
    by_id = row_by_id(rows)

    source = by_id["source_integral_lower_bound"]
    viscosity = by_id["retained_viscosity_lower_bound"]
    off_axis = by_id["off_axis_gain_absorption"]
    log_feedback = by_id["log_feedback_absorption"]
    clay_guard = by_id["clay_guard"]

    assert float(source["observed_value"]) == 82.0
    assert float(source["required_value"]) == 100.0
    assert float(source["margin_to_required"]) == -18.0
    assert "below_required" in normalize(source["status"])

    assert float(viscosity["observed_value"]) == 46.0
    assert float(viscosity["required_value"]) == 100.0
    assert float(viscosity["margin_to_required"]) == -54.0
    assert "deficit" in normalize(viscosity["status"])

    assert float(off_axis["observed_value"]) > float(off_axis["required_value"])
    assert float(log_feedback["observed_value"]) > float(log_feedback["required_value"])
    assert clay_guard["analytic_lemma_required"] == "MechanismExhaustionForFullClay"

    for row_id, row in by_id.items():
        assert row["claim_closed"] is False, row_id
        assert row["claim_proved"] is False, row_id
        assert row["promotion_allowed"] is False, row_id
        assert row["clay_navier_stokes_promoted"] is False, row_id
        assert row["blocker"], row_id

    summaries = [item for item in walk(payloads) if isinstance(item, dict)]
    assert any(item.get("source_deficit") == 18 for item in summaries)
    assert any(item.get("retained_viscosity_deficit") == 54 for item in summaries)
    for symbol in ("O", "R", "C", "S", "L", "P", "G", "F"):
        assert re.search(rf"\b{symbol}\b", text), f"missing control-card field {symbol}"


def test_source_viscosity_balance_agda_module_typechecks() -> None:
    result = subprocess.run(
        ["agda", "-i", ".", "-i", "DCHoTT-Agda", "-i", "cubical", str(AGDA_MODULE)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_source_viscosity_balance_agda_surface_names_and_counts() -> None:
    text = AGDA_MODULE.read_text(encoding="utf-8")
    for token in (
        "NSSprint150SourceViscosityBalanceReceipt",
        "SourceIntegralLowerBoundForMigratingMaximum",
        "RetainedViscosityLowerBoundAtMigratingMaximum",
        "SourceBeatsRetainedViscosityAtScaleDelta",
        "LocalizedSourceViscosityBalanceAtMigratingMaximum",
        "sourceIntegralComponentCount = 8",
        "retainedViscosityComponentCount = 7",
        "sourceViscosityAnalyticLemmaCount = 9",
        "sourceViscosityInequalityRowCount = 6",
        "sourceViscosityBlockerCount = 8",
        "sourceViscosityFalsePromotionGuardCount = 7",
        "sourceViscosityPromotionImpossibleHere",
    ):
        assert token in text
    assert "clayNavierStokesPromoted = true" not in text
    assert "full_clay_ns_solved = true" not in text
