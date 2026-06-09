from __future__ import annotations

import csv
import json
import math
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint116_option_b_crow_obstruction_audit.py"
SCALING_SCRIPT = REPO_ROOT / "scripts" / "ns_sprint116_crow_obstruction_scaling.py"

AUDIT_STEM = "ns_sprint116_option_b_crow_obstruction_audit"
SCALING_STEM = "ns_sprint116_crow_obstruction_scaling"
EXPECTED_DELTAS = (0.40, 0.30, 0.20, 0.10, 0.05)

EXPECTED_AUDIT_TRUE_FLAGS = (
    "thin_core_crow_route_obstructed",
)
EXPECTED_AUDIT_FALSE_FLAGS = (
    "clay",
)
REQUIRED_AUDIT_STRINGS = (
    "Option B",
    "Crow",
    "obstruction",
    "Clay",
    "promotion",
)


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
    md_paths = sorted(out_dir.glob("*.md"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    text = "\n".join(
        path.read_text(encoding="utf-8") for path in [*json_paths, *md_paths, *csv_paths]
    )
    return json_paths, md_paths, csv_paths, text


def load_json_artifacts(json_paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]


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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "hold"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "fail-closed"}:
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


def number_at(row: dict[str, Any], *names: str) -> float | None:
    value = value_at(row, *names)
    if value is None or value == "":
        return None
    return float(value)


def rows_from_artifacts(json_payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in flatten(json_payloads):
        if isinstance(item, dict) and number_at(item, "delta", "delta_over_b") is not None:
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return dedupe_rows(rows)


def dedupe_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: dict[float, dict[str, Any]] = {}
    for row in rows:
        delta = number_at(row, "delta", "delta_over_b")
        if delta is not None:
            deduped.setdefault(round(delta, 10), row)
    return list(deduped.values())


def ordered_values(rows: list[dict[str, Any]], *names: str) -> list[float]:
    pairs = sorted(
        (number_at(row, "delta", "delta_over_b"), number_at(row, *names)) for row in rows
    )
    assert all(delta is not None and value is not None for delta, value in pairs)
    return [value for _delta, value in pairs if value is not None]


def row_values(rows: list[dict[str, Any]], *names: str) -> list[float]:
    values = [number_at(row, *names) for row in rows]
    assert all(value is not None for value in values)
    return [value for value in values if value is not None]


def test_option_b_crow_obstruction_audit_runs_writes_flags_and_holds_clay(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / AUDIT_STEM
    result = run_script(AUDIT_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, md_paths, _csv_paths, artifact_text = read_artifacts(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    combined_text = "\n".join([result.stdout, result.stderr, artifact_text])

    for flag in EXPECTED_AUDIT_TRUE_FLAGS:
        assert bool_for_key(payloads, flag) is True, flag
    for flag in EXPECTED_AUDIT_FALSE_FLAGS:
        assert bool_for_key(payloads, flag) is False, flag
    summary_payloads = [payload for payload in payloads if isinstance(payload, dict)]
    assert summary_payloads
    clay_check = summary_payloads[-1]["bool_checks"]["clayNavierStokesPromoted"]
    assert clay_check["actual"] == "false"
    assert clay_check["passed"] is True
    for required in REQUIRED_AUDIT_STRINGS:
        assert re.search(re.escape(required), combined_text, re.IGNORECASE), required

    assert not re.search(r"clay[\w\s-]{0,80}(promoted|promotion)[\w\s-]{0,40}true", combined_text, re.I)
    assert not re.search(r"(promoted|promotion)[\w\s-]{0,80}clay[\w\s-]{0,40}true", combined_text, re.I)


def test_crow_obstruction_scaling_runs_rows_ratios_and_clay_hold(tmp_path: Path) -> None:
    out_dir = tmp_path / SCALING_STEM
    result = run_script(SCALING_SCRIPT, out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, md_paths, csv_paths, _artifact_text = read_artifacts(out_dir)
    assert json_paths, "scaling did not write JSON output"
    assert md_paths, "scaling did not write Markdown output"

    payloads = load_json_artifacts(json_paths)
    rows = rows_from_artifacts(payloads, csv_paths)
    observed_deltas = [round(number_at(row, "delta", "delta_over_b") or math.nan, 10) for row in rows]
    assert observed_deltas == [round(delta, 10) for delta in EXPECTED_DELTAS]

    reference_ratios = row_values(rows, "reference_flux_budget_over_e0", "reference_ratio")
    assert all(left > right for left, right in zip(reference_ratios, reference_ratios[1:]))

    obstruction_ratios = ordered_values(
        rows,
        "computed_obstruction_ratio",
        "obstruction_ratio",
        "computed_ratio",
    )
    assert obstruction_ratios[0] < obstruction_ratios[-1]

    assert bool_for_key(payloads, "option_b_crow_route_obstructed") is True
    assert bool_for_key(payloads, "clay", "clay_promoted", "clay_navier_stokes_promoted") is False
