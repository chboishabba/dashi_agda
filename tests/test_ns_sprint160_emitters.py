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
SPRINT = 160
EXPECTED_SCRIPT_COUNT = 3
EXPECTED_LANES = {2, 3, 4}
REQUIRED_TERMS = {
    "NoLocalClayMechanismSprintWithoutNewPDEMath",
    "SymmetricHouLuoPublicationIsolation",
    "Tier4 Maxwell/Hodge",
    "TierX Clay",
}
FALSE_CLAY_AND_PROMOTION_FLAGS = {
    "MechanismExhaustionForFullClayNS",
    "FullClayMechanismExhaustion",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "full_clay",
    "fullClay",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clay_navier_stokes_promoted",
    "clayNavierStokesPromoted",
    "promotion_allowed",
    "promotionAllowed",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
    "full_unification_promoted",
    "fullUnificationPromoted",
    "full_clay_ns_promoted",
    "fullClayNSPromoted",
    "continuum_ym_mass_gap_promoted",
    "continuumYMMassGapPromoted",
    "clay_yang_mills_promoted",
}


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def discover_sprint160_scripts() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint160_*.py") if path.is_file())


def run_script(script: Path, scratch_dir: Path) -> tuple[list[Any], str]:
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
        if path.suffix.lower() in {".json", ".csv", ".md"}
    )

    assert result.returncode == 0, text
    assert artifact_paths, text
    assert any(path.name.endswith("_summary.json") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.name.endswith("_rows.json") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_rows.csv") for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_manifest.json") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.suffix.lower() == ".md" for path in artifact_paths), [path.name for path in artifact_paths]

    payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in artifact_paths
        if path.suffix.lower() == ".json"
    ]
    return payloads, text


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


def boolean_keys(payloads: list[Any]) -> set[str]:
    keys: set[str] = set()
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        keys.update(key for key, value in item.items() if isinstance(value, bool))
    return keys


def test_sprint160_expected_worker_emitters_are_present() -> None:
    scripts = discover_sprint160_scripts()
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]


def test_sprint160_emitters_write_outputs_and_preserve_clay_guard(tmp_path: Path) -> None:
    scripts = discover_sprint160_scripts()
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]

    scratch_dir = OUTPUTS_DIR / ".pytest_ns_sprint160_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)

    lanes: set[int] = set()
    combined_text = ""
    try:
        for script in scripts:
            payloads, text = run_script(script, scratch_dir)
            combined_text += text
            script_lanes = lane_values(payloads)
            assert len(script_lanes) == 1, script_lanes
            lanes |= script_lanes

            assert any(item.get("sprint") == SPRINT for item in walk(payloads) if isinstance(item, dict)), text
            assert any("control_card" in item for item in walk(payloads) if isinstance(item, dict)), text
            assert any(bool_values(payloads, "validation_passed")), text
            assert all(value is True for value in bool_values(payloads, "validation_passed")), script.name

            for key in boolean_keys(payloads):
                if key in FALSE_CLAY_AND_PROMOTION_FLAGS:
                    assert all(value is False for value in bool_values(payloads, key)), (script.name, key)
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    assert lanes == EXPECTED_LANES
    for term in REQUIRED_TERMS:
        assert term in combined_text
