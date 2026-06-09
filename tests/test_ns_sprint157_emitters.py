from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
SPRINT = 157
EXPECTED_LANES = {2, 3, 4}


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def discover_sprint157_scripts() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint157_*.py") if path.is_file())


def run_script(script: Path, scratch_dir: Path) -> tuple[list[Any], list[Path], str]:
    out_dir = scratch_dir / script.stem
    result = subprocess.run(
        [sys.executable, str(script), "--repo-root", str(REPO_ROOT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    artifact_paths = sorted(path for path in out_dir.glob("*") if path.is_file()) if out_dir.exists() else []
    text = result.stdout + result.stderr + "\n".join(
        path.read_text(encoding="utf-8", errors="replace")
        for path in artifact_paths
        if path.suffix in {".json", ".csv", ".md"}
    )
    assert result.returncode == 0, text
    assert artifact_paths, text
    assert any(path.name.endswith("_summary.json") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_rows.json") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_rows.csv") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_manifest.json") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.suffix == ".md" for path in artifact_paths), [path.name for path in artifact_paths]
    payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in artifact_paths
        if path.suffix == ".json"
    ]
    return payloads, artifact_paths, text


def bool_values(payloads: list[Any], key: str) -> list[bool]:
    values: list[bool] = []
    for item in walk(payloads):
        if isinstance(item, dict) and isinstance(item.get(key), bool):
            values.append(item[key])
    return values


def lane_values(payloads: list[Any]) -> set[int]:
    lanes: set[int] = set()
    for item in walk(payloads):
        if isinstance(item, dict) and isinstance(item.get("lane"), int):
            lanes.add(item["lane"])
    return lanes


def test_sprint157_expected_worker_emitters_are_present() -> None:
    scripts = discover_sprint157_scripts()
    assert [path.name for path in scripts] == [
        "ns_sprint157_bkm_integral_estimate.py",
        "ns_sprint157_continuation_bridge.py",
        "ns_sprint157_symmetric_hou_luo_regular_class.py",
    ]


def test_sprint157_emitters_write_outputs_and_preserve_clay_guard(tmp_path: Path) -> None:
    scripts = discover_sprint157_scripts()
    scratch_dir = OUTPUTS_DIR / ".pytest_ns_sprint157_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)

    lanes: set[int] = set()
    observed_bkm_integral = False
    observed_continuation = False
    observed_symmetric_bkm = False
    try:
        for script in scripts:
            payloads, _, text = run_script(script, scratch_dir)
            script_lanes = lane_values(payloads)
            assert len(script_lanes) == 1, script_lanes
            lanes |= script_lanes

            assert any(item.get("sprint") == SPRINT for item in walk(payloads) if isinstance(item, dict)), text
            assert any("control_card" in item for item in walk(payloads) if isinstance(item, dict)), text
            assert all(value is False for value in bool_values(payloads, "full_clay_ns_solved")), script.name
            assert all(value is False for value in bool_values(payloads, "fullClayNSSolved")), script.name
            assert all(value is False for value in bool_values(payloads, "clay_navier_stokes_promoted")), script.name
            assert all(value is False for value in bool_values(payloads, "promotion_allowed")), script.name

            observed_bkm_integral |= any(bool_values(payloads, "BKMIntegralEstimate"))
            observed_continuation |= any(bool_values(payloads, "ContinuationTheoremBridge"))
            observed_symmetric_bkm |= any(bool_values(payloads, "SymmetricHouLuoBKMFinite"))
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    assert lanes == EXPECTED_LANES
    assert observed_bkm_integral
    assert observed_continuation
    assert observed_symmetric_bkm
