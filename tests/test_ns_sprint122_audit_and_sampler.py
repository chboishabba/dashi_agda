from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"


def find_script(kind: str, preferred: tuple[str, ...]) -> Path:
    for name in preferred:
        path = SCRIPTS_DIR / name
        if path.exists():
            return path

    matches = sorted(SCRIPTS_DIR.glob(f"ns_sprint122*{kind}*.py"))
    assert matches, f"required Sprint 122 {kind} script is missing"
    assert len(matches) == 1, f"ambiguous Sprint 122 {kind} scripts: {matches}"
    return matches[0]


AUDIT_SCRIPT_NAMES = (
    "ns_sprint122_rotating_persistence_audit.py",
    "ns_sprint122_dynamic_bound_audit.py",
    "ns_sprint122_dynamic_persistence_audit.py",
)
SAMPLER_SCRIPT_NAMES = (
    "ns_sprint122_phase_lag_dynamics_sampler.py",
    "ns_sprint122_dynamic_bound_sampler.py",
    "ns_sprint122_dynamic_persistence_sampler.py",
)


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


def scalar_int_for_key(payloads: list[Any], *names: str) -> int:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[int] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in normalized_names:
                parsed = intish(value)
                if parsed is not None:
                    matches.append(parsed)
    assert matches, f"missing scalar integer-like field for {names}"
    return matches[-1]


def test_dynamic_bound_audit_runs_and_records_fail_closed_summary(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint122_dynamic_bound_audit"
    result = run_script(find_script("audit", AUDIT_SCRIPT_NAMES), out_dir)
    assert result.returncode in {0, 1}, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert not csv_paths, "audit should not need CSV output"
    assert md_paths, "audit did not write Markdown output"

    payloads = load_json(summary_json_paths(json_paths))
    assert scalar_bool_for_key(
        payloads,
        "coherent",
        "audit_coherent",
        "auditCoherent",
        "ledger_coherent_fail_closed",
        "ledgerCoherentFailClosed",
    ) is True
    assert scalar_bool_for_key(
        payloads,
        "clay",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
    ) is False
    assert scalar_bool_for_key(
        payloads,
        "promotion",
        "promotion_decision",
        "promotionDecision",
        "promotion_ready",
        "promotionReady",
    ) is False


def test_dynamic_sampler_counts_favorable_rows_and_keeps_fail_closed_fields(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "ns_sprint122_dynamic_bound_sampler"
    result = run_script(find_script("sampler", SAMPLER_SCRIPT_NAMES), out_dir)
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"

    payloads = load_json(summary_json_paths(json_paths))
    assert scalar_int_for_key(
        payloads,
        "favorable_dynamic_rows_count",
        "favorableDynamicRowsCount",
    ) > 0
    assert scalar_bool_for_key(
        payloads,
        "non_circular_dynamic_bound_established",
        "nonCircularDynamicBoundEstablished",
    ) is False
    assert scalar_bool_for_key(
        payloads,
        "persistence_bound_closed",
        "persistenceBoundClosed",
    ) is False
    assert scalar_bool_for_key(
        payloads,
        "clay",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
    ) is False
