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
STEM = "ns_sprint149_energy_width_lower_bound"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint149ScalingConsistencyGateReceipt.agda"
)

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
FALSE_FLAG_NAMES = {
    "energy_width_lower_bound_proved",
    "alpha_less_than_one_proved",
    "scaling_consistency_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
}
TRUE_FLAG_NAMES = {
    "gronwall_closure_conditional",
}
EXPECTED_ROW_IDS = {
    "delta_power_law_normalization",
    "energy_monotonicity_width_constraint",
    "enstrophy_width_constraint",
    "viscous_lower_width_candidate",
    "energy_alone_alpha_less_than_one_gap",
    "scaling_consistency_theorem_absent",
    "conditional_gronwall_closure",
}
TRUE_COMPLETION_PATTERNS = (
    re.compile(
        r'"(?:energy_width_lower_bound_proved|alpha_less_than_one_proved|'
        r'scaling_consistency_proved|full_clay|full_clay_ns_solved|'
        r'clay_navier_stokes_promoted|promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:energyWidthLowerBoundProved|alphaLessThanOneProved|"
        r"scalingConsistencyProved|fullClay|clayNavierStokesPromoted|"
        r"promotionAllowed)\s*=\s*true\b"
    ),
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


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_markers = {
        "artifact_id",
        "claim_id",
        "gate_id",
        "guard_id",
        "obstruction_id",
        "row_id",
        "status",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_markers for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(value: Any, *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        for key, candidate in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(candidate)
                if parsed is not None:
                    values.append(parsed)
    return values


def assert_control_card_present(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        if CONTROL_CARD_KEYS.issubset({str(key) for key in item}):
            return
        card = item.get("control_card") or item.get("control-card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
    normalized_text = normalize(text)
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalized_text]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def run_energy_width_lower_bound(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
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


def test_energy_width_lower_bound_emits_fail_closed_gate_artifacts(tmp_path: Path) -> None:
    payloads, rows, text, out_dir = run_energy_width_lower_bound(tmp_path)
    combined = "\n".join([text, compact(payloads), compact(rows)])
    row_ids = {
        normalize(value)
        for row in rows
        for key, value in row.items()
        if normalize(key) in {"row_id", "claim_id", "gate_id", "guard_id", "obstruction_id"}
    }

    assert out_dir.name == STEM
    assert "energy_width_lower_bound" in combined
    assert "scaling_consistency" in combined
    assert_control_card_present(payloads, text)

    missing_row_ids = {normalize(row_id) for row_id in EXPECTED_ROW_IDS} - row_ids
    assert not missing_row_ids, f"missing row ids {sorted(missing_row_ids)}: {row_ids}"

    for name in FALSE_FLAG_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        assert values, f"missing false flag {name}\n{text}"
        assert all(value is False for value in values), (name, values)

    for name in TRUE_FLAG_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        assert values, f"missing true flag {name}\n{text}"
        assert any(value is True for value in values), (name, values)

    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_scaling_consistency_receipt_records_gate_names_false_flags_and_blockers() -> None:
    if not RECEIPT.is_file():
        pytest.skip(f"{RECEIPT.relative_to(REPO_ROOT)} is not present yet")

    text = RECEIPT.read_text(encoding="utf-8")
    normalized = normalize(text)
    required_terms = [
        "NSSprint149ScalingConsistencyGateReceipt",
        "EnergyWidthLowerBound",
        "ScalingConsistency",
        "ScalingConsistencyFalsePromotionGuard",
        "blocker",
        "guard",
    ]
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    required_false_assignments = [
        "energyWidthLowerBoundProved",
        "alphaLessThanOneProved",
        "ScalingConsistencyForHouLuoConcentrationProved",
        "full_clay_ns_solved",
        "clayNavierStokesPromoted",
    ]
    for name in required_false_assignments:
        assert agda_bool_assignment(text, name, False), name

    assert agda_bool_assignment(text, "gronwallClosureConditional", True), (
        "gronwallClosureConditional"
    )
    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern
