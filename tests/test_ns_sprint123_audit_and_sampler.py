from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"

AUDIT_SCRIPT_NAMES = (
    "ns_sprint123_dwell_audit.py",
    "ns_sprint123_favorable_dwell_audit.py",
    "ns_sprint123_phase_locking_audit.py",
)
SAMPLER_SCRIPT_NAMES = (
    "ns_sprint123_dwell_sampler.py",
    "ns_sprint123_favorable_dwell_sampler.py",
    "ns_sprint123_phase_locking_dwell_sampler.py",
)


def find_script(kind: str, preferred: tuple[str, ...]) -> Path:
    for name in preferred:
        path = SCRIPTS_DIR / name
        if path.exists():
            return path

    matches = sorted(SCRIPTS_DIR.glob(f"ns_sprint123*{kind}*.py"))
    assert matches, f"required Sprint 123 {kind} script is missing"
    assert len(matches) == 1, f"ambiguous Sprint 123 {kind} scripts: {matches}"
    return matches[0]


def run_script(script: Path, out_dir: Path) -> subprocess.CompletedProcess[str]:
    assert script.exists(), f"required script is missing: {script}"
    return subprocess.run(
        ["python3", str(script), "--out-dir", str(out_dir)],
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


def summary_json_paths(paths: list[Path]) -> list[Path]:
    summaries = [path for path in paths if "summary" in path.name]
    assert summaries, f"missing summary JSON in {paths}"
    return summaries


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalize_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def value_for_key(payloads: list[Any], *names: str) -> Any:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[Any] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in normalized_names and not isinstance(value, (dict, list)):
                matches.append(value)
    assert matches, f"missing scalar field for {names}"
    return matches[-1]


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "closed", "met", "coherent"}:
            return True
        if lowered in {"false", "0", "no", "open", "blocked", "unmet", "hold"}:
            return False
    return None


def intish(value: Any) -> int | None:
    if value is None or value == "":
        return None
    try:
        as_float = float(value)
    except (TypeError, ValueError):
        return None
    if as_float.is_integer():
        return int(as_float)
    return None


def scalar_bool_for_key(payloads: list[Any], *names: str) -> bool:
    parsed = boolish(value_for_key(payloads, *names))
    assert parsed is not None, f"field is not boolean-like for {names}"
    return parsed


def scalar_int_for_key(payloads: list[Any], *names: str) -> int:
    parsed = intish(value_for_key(payloads, *names))
    assert parsed is not None, f"field is not integer-like for {names}"
    return parsed


def scalar_string_for_key(payloads: list[Any], *names: str) -> str:
    value = value_for_key(payloads, *names)
    assert isinstance(value, str), f"field is not string-like for {names}"
    return value


def test_sprint123_audit_runs_and_records_hold_summary(tmp_path: Path) -> None:
    out_dir = tmp_path / "ns_sprint123_audit"
    result = run_script(find_script("audit", AUDIT_SCRIPT_NAMES), out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert not csv_paths, "audit should not need CSV output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json(summary_json_paths(json_paths))
    assert scalar_bool_for_key(payloads, "ledger_coherent_fail_closed") is True
    assert scalar_bool_for_key(payloads, "clay_navier_stokes_promoted") is False
    assert scalar_string_for_key(payloads, "promotion_decision") == "hold"


def test_sprint123_dwell_sampler_writes_artifacts_and_false_claims(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint123_dwell_sampler"
    result = run_script(find_script("sampler", SAMPLER_SCRIPT_NAMES), out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"

    payloads = load_json(summary_json_paths(json_paths))
    assert scalar_int_for_key(payloads, "favorable_dwell_rows_count") > 0
    assert scalar_bool_for_key(payloads, "nse_derived_phase_locking_established") is False
    assert scalar_bool_for_key(payloads, "favorable_window_lower_bound_closed") is False
    assert scalar_bool_for_key(payloads, "clay") is False
