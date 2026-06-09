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
SCRIPT_DIR = REPO_ROOT / "scripts"

SCALING_STEM = "ns_sprint149_scaling_consistency_gate"
LINEARIZATION_STEM = "ns_sprint149_linearization_spectrum_probe"

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
SCALING_REQUIRED_ROW_IDS = {
    "beta_positive_scaling_target",
    "corrected_time_available_factor",
    "gronwall_closable_growth_ode",
    "explicit_initial_data_support",
    "source_lower_bound_numerical_support",
    "self_similar_profile_analysis_missing",
    "energy_width_lower_bound_missing",
    "symmetric_hou_luo_bkm_conditional",
    "clay_guard",
}
LINEARIZATION_EXPECTED_BETAS = {-1.0, -0.5, -0.25, 0.0, 0.125, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5}
ROW_KEY_NAMES = {
    "case_id",
    "gate_id",
    "id",
    "probe_id",
    "row_id",
    "scenario_id",
    "status",
}

TRUE_PROMOTION_OR_THEOREM_PATTERNS = (
    re.compile(
        r'"(?:full_clay_ns_solved|clay_navier_stokes_promoted|promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r'"(?:claim_proved|claim_proven|self_similar_profile_analysis_proved|scaling_consistency_proved|beta_positive_scaling_proved|symmetric_hou_luo_bkm_finite)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:full[_\s-]*clay[_\s-]*ns[_\s-]*solved|clay[_\s-]*navier[_\s-]*stokes[_\s-]*promoted|promotion[_\s-]*allowed)\b\s*[:=]\s*true\b",
        re.IGNORECASE,
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
    normalized_row_keys = {normalize(name) for name in ROW_KEY_NAMES}
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in normalized_row_keys for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_key_terms(payloads: list[Any], *terms: str) -> list[bool]:
    wanted = tuple(normalize(term) for term in terms)
    values: list[bool] = []
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            parsed = as_bool(value)
            if parsed is not None and all(term in normalize(key) for term in wanted):
                values.append(parsed)
    return values


def bool_values_for_names(payloads: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            parsed = as_bool(value)
            if parsed is not None and normalize(key) in wanted:
                values.append(parsed)
    return values


def row_ids(rows: list[dict[str, Any]]) -> set[str]:
    ids: set[str] = set()
    for row in rows:
        for key in ("row_id", "gate_id", "probe_id", "case_id", "scenario_id", "id"):
            value = row.get(key)
            if isinstance(value, str) and value.strip():
                ids.add(normalize(value))
                break
    return ids


def row_id_matching(ids: set[str], *terms: str) -> list[str]:
    wanted = tuple(normalize(term) for term in terms)
    return [row_id for row_id in ids if all(term in row_id for term in wanted)]


def run_sprint149_script(tmp_path: Path, stem: str) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    script = SCRIPT_DIR / f"{stem}.py"
    if not script.is_file():
        pytest.skip(f"{script.relative_to(REPO_ROOT)} is not present yet")

    out_dir = tmp_path / stem
    result = subprocess.run(
        [
            sys.executable,
            str(script),
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
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, artifact_text
    return payloads, rows, artifact_text, out_dir


def assert_control_card(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        if CONTROL_CARD_KEYS.issubset({str(key) for key in item}):
            return
        card = item.get("control_card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
    normalized_text = normalize(text)
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalized_text]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def assert_false_theorem_and_promotion_flags(payloads: list[Any], text: str) -> None:
    promotion_values = bool_values_for_names(
        payloads,
        "promotion_allowed",
        "clay_navier_stokes_promoted",
        "full_clay_ns_solved",
    )
    theorem_values = bool_values_for_names(
        payloads,
        "claim_proved",
        "claim_proven",
        "self_similar_profile_analysis_proved",
        "scaling_consistency_proved",
        "beta_positive_scaling_proved",
        "symmetric_hou_luo_bkm_finite",
    )
    assert promotion_values, f"missing explicit promotion/Clay flags\n{text}"
    assert theorem_values, f"missing explicit theorem/proof flags\n{text}"
    assert all(value is False for value in promotion_values), promotion_values
    assert all(value is False for value in theorem_values), theorem_values
    for pattern in TRUE_PROMOTION_OR_THEOREM_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_true_support_flag(payloads: list[Any], text: str, *terms: str) -> None:
    values = bool_values_for_key_terms(payloads, *terms)
    assert values, f"missing support flag with terms {terms}\n{text}"
    assert any(value is True for value in values), values


def assert_false_flags(payloads: list[Any], text: str, *terms: str) -> None:
    values = bool_values_for_key_terms(payloads, *terms)
    assert values, f"missing false flag with terms {terms}\n{text}"
    assert all(value is False for value in values), values


def beta_values(rows: list[dict[str, Any]]) -> set[float]:
    values: set[float] = set()
    for row in rows:
        if "beta" in row:
            values.add(float(row["beta"]))
    return values


def test_scaling_consistency_gate_outputs_rows_gates_and_fail_closed_flags(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint149_script(tmp_path, SCALING_STEM)
    ids = row_ids(rows)
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert out_dir.name == SCALING_STEM
    assert "scaling" in combined
    assert "consistency" in combined
    assert "gate" in combined
    assert SCALING_REQUIRED_ROW_IDS.issubset(ids), ids
    assert_control_card(payloads, text)
    assert_true_support_flag(payloads, text, "explicit", "initial", "data", "class")
    assert_true_support_flag(payloads, text, "correct", "growth", "ode", "closable")
    assert_true_support_flag(payloads, text, "migration", "threshold", "conditionally")
    assert_false_flags(payloads, text, "scaling", "consistency", "proved")
    assert_false_flags(payloads, text, "beta", "positive", "scaling", "proved")
    assert_false_theorem_and_promotion_flags(payloads, text)


def test_linearization_spectrum_probe_outputs_rows_gates_and_fail_closed_flags(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint149_script(tmp_path, LINEARIZATION_STEM)
    ids = row_ids(rows)
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert out_dir.name == LINEARIZATION_STEM
    assert "linearization" in combined
    assert "spectrum" in combined
    assert "probe" in combined
    assert beta_values(rows) == LINEARIZATION_EXPECTED_BETAS
    assert_control_card(payloads, text)
    assert_true_support_flag(payloads, text, "linearization", "probe", "complete")
    assert_true_support_flag(payloads, text, "beta", "positive", "candidate", "seen")
    assert_false_flags(payloads, text, "scaling", "consistency", "proved")
    assert_false_flags(payloads, text, "self", "similar", "profile", "analysis", "proved")
    assert_false_theorem_and_promotion_flags(payloads, text)
