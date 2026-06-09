from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint147_migration_threshold_ode_scan"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSMigrationInitiationThresholdReceipt.agda"
)
CONSTANTS_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSMigrationInitiationThresholdConstantsReceipt.agda"
)

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
FALSE_FLAG_NAMES = {
    "migration_threshold_gate_closed",
    "migration_initiation_threshold_proved",
    "migration_initiation_threshold_ode_scan_proved",
    "maximum_location_migration_lemma_proved",
    "global_barrier_closed",
    "global_proof",
    "global_proof_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "clayNavierStokesPromoted",
    "promotion_allowed",
}
TRUE_CLOSURE_PATTERNS = (
    re.compile(
        r'"(?:full_clay_ns_solved|clay_navier_stokes_promoted|promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r'"(?:global_proof|global_proof_closed|global_barrier_closed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r'"(?:migration_[a-z_]*proved|migration_[a-z_]*closed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(r"\b(?:full_clay_ns_solved|clayNavierStokesPromoted|promotionAllowed)\s*=\s*true\b"),
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


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def compact(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_markers = {
        "row_id",
        "regime_id",
        "scenario_id",
        "toy_regime",
        "status",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_markers for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(values: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    found: list[bool] = []
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(value)
                if parsed is not None:
                    found.append(parsed)
    return found


def run_ode_scan(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    if not SCRIPT.is_file():
        pytest.skip(f"{SCRIPT.relative_to(REPO_ROOT)} is not present yet")

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

    artifact_paths = sorted(out_dir.glob("*")) if out_dir.exists() else []
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    summary_paths = [path for path in json_paths if "summary" in normalize(path.name)]
    rows_paths = [path for path in artifact_paths if "row" in normalize(path.name)]
    text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )

    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert summary_paths, text
    assert rows_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in [*summary_paths, *rows_paths, *md_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, text
    return payloads, rows, text, out_dir


def row_initiates(row: dict[str, Any]) -> bool:
    for key, value in row.items():
        key_text = normalize(key)
        parsed = as_bool(value)
        if parsed is True and (
            "initiat" in key_text
            or "threshold_cross" in key_text
            or "toy_regime_cross" in key_text
        ):
            return True
    row_text = compact(row)
    return (
        "toy" in row_text
        and ("initiat" in row_text or "threshold_cross" in row_text)
        and not any(term in row_text for term in ("no_initiation", "does_not_initiate"))
    )


def assert_control_card_present(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if isinstance(item, dict):
            keys = {str(key) for key in item}
            if CONTROL_CARD_KEYS.issubset(keys):
                return
            card = item.get("control_card")
            if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
                return
    normalized_text = normalize(text)
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalized_text]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def test_migration_threshold_ode_scan_writes_fail_closed_artifacts(tmp_path: Path) -> None:
    payloads, rows, text, out_dir = run_ode_scan(tmp_path)
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert out_dir.name == STEM
    assert "migration" in combined
    assert "threshold" in combined
    assert "ode" in combined
    assert "toy" in combined
    assert any(row_initiates(row) for row in rows), rows
    assert_control_card_present(payloads, text)

    for name in FALSE_FLAG_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        if values:
            assert all(value is False for value in values), (name, values)
    assert bool_values_for_keys(
        [payloads, rows],
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
    ), text
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_migration_threshold_receipt_records_gate_names_and_false_promotion_flags() -> None:
    if not RECEIPT.is_file():
        pytest.skip(f"{RECEIPT.relative_to(REPO_ROOT)} is not present yet")

    text = RECEIPT.read_text(encoding="utf-8")
    normalized = normalize(text)
    required_terms = [
        "NSMigrationInitiationThresholdReceipt",
        "MigrationInitiationThresholdForLargeData",
        "MigrationInitiationThresholdSurface",
        "MigrationInitiationORCSLPGF",
        "MaximumLocationMigrationLemma",
        "MigrationInitiationFalsePromotionGuard",
    ]
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    required_false_assignments = [
        "MaximumLocationMigrationExclusionForVBarrier",
        "MigrationInitiationThresholdForLargeData",
        "migrationDrivenBlowupStructureClayPromoted",
        "full_clay_ns_solved",
        "clayNavierStokesPromoted",
    ]
    for name in required_false_assignments:
        assert re.search(rf"\b{re.escape(name)}\s*=\s*false\b", text), name

    false_guard_terms = [
        "doNot",
        "Promote",
        "Clay",
    ]
    for term in false_guard_terms:
        assert normalize(term) in normalized, term
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_migration_threshold_constants_receipt_records_quantitative_obligations() -> None:
    if not CONSTANTS_RECEIPT.is_file():
        pytest.skip(f"{CONSTANTS_RECEIPT.relative_to(REPO_ROOT)} is not present yet")

    text = CONSTANTS_RECEIPT.read_text(encoding="utf-8")
    normalized = normalize(text)
    required_terms = [
        "NSMigrationInitiationThresholdConstantsReceipt",
        "MigrationThresholdConstantObligationSurface",
        "sourceIntegralRequiredLowerBound",
        "sourceIntegralObservedLowerBound",
        "viscosityRetentionRequiredLowerBound",
        "viscosityRetentionObservedLowerBound",
        "sourceIntegralBelowRequired",
        "viscosityRetentionBelowRequired",
        "sourceIntegralDominatesViscositySuppression",
        "quantitativeConstantsSufficientForMigrationInitiation",
        "migrationThresholdConstantCountPackage",
    ]
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    exact_count_assignments = {
        "migrationThresholdConstantCount": "7",
        "migrationThresholdRequiredEstimateCount": "5",
        "migrationThresholdInequalityDirectionCount": "4",
        "migrationThresholdFailClosedFlagCount": "5",
    }
    for name, value in exact_count_assignments.items():
        assert re.search(rf"\b{re.escape(name)}\s*:\s*Nat\b", text), name
        assert re.search(rf"\b{re.escape(name)}\s*=\s*{value}\b", text), name

    required_false_assignments = [
        "sourceIntegralDominatesViscositySuppression",
        "viscositySuppressionUniformlyAbsorbed",
        "offAxisGainUniformlyBounded",
        "logFeedbackUniformlyAbsorbed",
        "quantitativeConstantsSufficientForMigrationInitiation",
    ]
    for name in required_false_assignments:
        assert re.search(rf"\b{re.escape(name)}\s*=\s*false\b", text), name

    assert re.search(r"\bquantitativeConstantsFailClosed\s*=\s*true\b", text)
    assert "sourceIntegralObserved <= sourceIntegralRequired" in text
    assert "viscosityRetainedObserved <= viscosityRetainedRequired" in text
