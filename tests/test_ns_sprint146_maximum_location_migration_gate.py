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
STEM = "ns_sprint146_maximum_location_migration_gate"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

REQUIRED_ROW_IDS = {
    "pinned_center",
    "symmetric_twin_peak_migration",
    "positive_feedback_candidate",
    "regularity_partial_recovery_branch",
}

TRUE_CLOSURE_PATTERNS = (
    re.compile(r'"maximum_location_migration_lemma_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"migration_gate_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_barrier_closed"\s*:\s*true\b', re.IGNORECASE),
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


def run_gate(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
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


def test_maximum_location_migration_gate_outputs_named_rows_and_files(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_gate(tmp_path)
    combined = "\n".join([text, compact(payloads), compact(rows)])
    by_id = row_by_id(rows)

    assert out_dir.name == STEM
    assert set(by_id) == REQUIRED_ROW_IDS
    assert "MaximumLocationMigrationLemma" in text
    assert "source_sign" in combined
    assert "blockers" in combined
    assert "status" in combined
    assert "pinned_center" in combined
    assert "symmetric_twin_peak_migration" in combined
    assert "positive_feedback_candidate" in combined
    assert "regularity_partial_recovery_branch" in combined

    assert_true_flags(payloads, text, "artifact_complete", "invariants_passed")
    assert_false_flags(
        payloads,
        text,
        "maximum_location_migration_lemma_proved",
        "migration_gate_closed",
        "comparison_envelope_available",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
    )
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_maximum_location_migration_gate_records_status_blockers_and_source_logic(
    tmp_path: Path,
) -> None:
    _payloads, rows, text, _out_dir = run_gate(tmp_path)
    by_id = row_by_id(rows)

    pinned = by_id["pinned_center"]
    twin = by_id["symmetric_twin_peak_migration"]
    feedback = by_id["positive_feedback_candidate"]
    regularity = by_id["regularity_partial_recovery_branch"]

    assert pinned["status"] == "SUPPORT_LOCAL_ONLY"
    assert pinned["source_sign"] == "negative"
    assert pinned["supports_pinned_center_only"] is True
    assert float(pinned["maximum_location_velocity_proxy"]) == 0.0

    assert twin["status"] == "BLOCKED_BY_MAXIMUM_LOCATION_MIGRATION"
    assert twin["source_sign"] == "negative"
    assert twin["symmetric_migration_row"] is True
    assert abs(float(twin["maximum_location_velocity_proxy"])) > 0.0

    assert feedback["status"] == "BLOCKED_BY_POSITIVE_SOURCE_FEEDBACK"
    assert feedback["source_sign"] == "positive"
    assert feedback["positive_feedback_row"] is True
    assert float(feedback["source_term_proxy"]) > 0.0

    assert regularity["status"] == "PARTIAL_RECOVERY_BLOCKED"
    assert regularity["source_sign"] == "positive"
    assert regularity["regularity_partial_recovery_row"] is True
    assert float(regularity["regularity_budget_proxy"]) > float(feedback["regularity_budget_proxy"])

    for row_id, row in by_id.items():
        assert "MaximumLocationMigrationLemma" in str(row["blockers"]), row
        assert row["source_sign_logic"], row
        assert row["source_sign_matches_expected"] is True, row
        assert row["migration_gate_closed"] is False, row
        assert row["clay_navier_stokes_promoted"] is False, row
        assert "partial_z^2 psi1" in row["source_sign_logic"], row_id

    assert "regularity_budget_does_not_supply_source_sign" in text
