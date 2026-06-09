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
STEM = "ns_sprint147_migration_initiation_threshold"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

REQUIRED_ROW_IDS = {
    "source_integral_threshold",
    "symmetry_plane_diffusion_baseline",
    "off_axis_gain",
    "viscosity_suppression",
    "log_supercritical_feedback",
    "smooth_finite_energy_admissibility",
    "clay_promotion_guard",
}

REQUIRED_GATES = {
    "pure_diffusion_at_symmetry_plane",
    "maximum_location_migration_exclusion",
    "migration_initiation_threshold_proved",
    "migration_threshold_available",
    "migration_threshold_closed",
    "blowup_existence_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}

TRUE_CLOSURE_PATTERNS = (
    re.compile(r'"maximum_location_migration_exclusion"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"migration_initiation_threshold_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"migration_threshold_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"blowup_existence_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
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


def compact(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


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


def keys_seen(payloads: list[Any]) -> set[str]:
    keys: set[str] = set()
    for item in walk(payloads):
        if isinstance(item, dict):
            keys.update(normalize(key) for key in item)
    return keys


def run_threshold(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    assert SCRIPT.exists(), f"expected Sprint 147 script at {SCRIPT}"

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


def assert_false_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing flags for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_true_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing flags for {names}\n{text}"
    assert all(value is True for value in values), values


def test_migration_initiation_threshold_emits_required_artifacts_and_rows(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_threshold(tmp_path)
    combined = "\n".join([text, compact(payloads), compact(rows)])
    by_id = row_by_id(rows)

    assert out_dir.name == STEM
    assert set(by_id) == REQUIRED_ROW_IDS
    assert "MigrationInitiationThreshold" in text
    assert "migration_initiation_threshold" in combined
    assert "source_integral_threshold" in combined
    assert "symmetry_plane_diffusion_baseline" in combined
    assert "off_axis_gain" in combined
    assert "viscosity_suppression" in combined
    assert "log_supercritical_feedback" in combined
    assert "smooth_finite_energy_admissibility" in combined
    assert "clay_promotion_guard" in combined

    assert REQUIRED_GATES <= keys_seen(payloads)
    assert_true_flags(
        payloads,
        text,
        "artifact_complete",
        "invariants_passed",
        "pure_diffusion_at_symmetry_plane",
    )
    assert_false_flags(
        payloads,
        text,
        "maximum_location_migration_exclusion",
        "migration_initiation_threshold_proved",
        "migration_threshold_available",
        "migration_threshold_closed",
        "blowup_existence_proved",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
    )
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_migration_initiation_threshold_records_gate_logic_and_orcslpgf(
    tmp_path: Path,
) -> None:
    payloads, rows, text, _out_dir = run_threshold(tmp_path)
    by_id = row_by_id(rows)
    combined = "\n".join([text, compact(payloads), compact(rows)])

    source = by_id["source_integral_threshold"]
    plane = by_id["symmetry_plane_diffusion_baseline"]
    gain = by_id["off_axis_gain"]
    viscosity = by_id["viscosity_suppression"]
    log_feedback = by_id["log_supercritical_feedback"]
    admissibility = by_id["smooth_finite_energy_admissibility"]
    clay_guard = by_id["clay_promotion_guard"]

    assert source["supports_threshold"] is False
    assert source["obstructs_threshold"] is True
    assert "threshold" in normalize(source.get("status", ""))

    assert plane["pure_diffusion_at_symmetry_plane"] is True
    assert plane["supports_threshold"] is True
    assert "pure_diffusion" in normalize(plane.get("status", ""))

    assert gain["obstructs_threshold"] is True
    assert viscosity["obstructs_threshold"] is True
    assert log_feedback["obstructs_threshold"] is True

    assert admissibility["supports_threshold"] is True
    assert admissibility["migration_initiation_threshold_proved"] is False

    assert clay_guard["blowup_existence_proved"] is False
    assert clay_guard["full_clay_ns_solved"] is False
    assert clay_guard["clay_navier_stokes_promoted"] is False

    for row_id, row in by_id.items():
        assert row["pure_diffusion_at_symmetry_plane"] is True, row_id
        assert row["maximum_location_migration_exclusion"] is False, row_id
        assert row["migration_initiation_threshold_proved"] is False, row_id
        assert row["blowup_existence_proved"] is False, row_id
        assert row["full_clay_ns_solved"] is False, row_id
        assert row["clay_navier_stokes_promoted"] is False, row_id
        assert isinstance(row.get("blockers"), list), row

    for symbol in ("O", "R", "C", "S", "L", "P", "G", "F"):
        assert re.search(rf"\b{symbol}\b", text), f"missing O/R/C/S/L/P/G/F field {symbol}"

    assert "fail_closed_migration_initiation_threshold_not_proved" in combined
    assert "blowup_existence_proved_false" in combined
