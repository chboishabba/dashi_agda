from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
SPRINT = 161
EXPECTED_SCRIPT_NAMES = {
    "ns_sprint161_analytic_attempt_boundary.py",
    "ns_sprint161_defect_monotonicity_gap.py",
    "ns_sprint161_critical_profile_taxonomy.py",
}
REQUIRED_TERMS = {
    "analytic attempt boundary",
    "defect monotonicity gap",
    "critical profile taxonomy",
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
}


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def discover_sprint161_scripts() -> list[Path]:
    return sorted(
        path
        for path in SCRIPT_DIR.glob("ns_sprint161_*.py")
        if path.is_file() and path.name in EXPECTED_SCRIPT_NAMES
    )


def run_script(script: Path, out_dir: Path) -> tuple[list[Any], str, list[Path]]:
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
    assert any(path.suffix.lower() == ".json" for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.suffix.lower() == ".csv" for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.suffix.lower() == ".md" for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_manifest.json") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]

    payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in artifact_paths
        if path.suffix.lower() == ".json"
    ]
    return payloads, text, artifact_paths


def bool_values(payloads: list[Any], key: str) -> list[bool]:
    values: list[bool] = []
    for item in walk(payloads):
        if isinstance(item, dict) and isinstance(item.get(key), bool):
            values.append(item[key])
    return values


def boolean_keys(payloads: list[Any]) -> set[str]:
    keys: set[str] = set()
    for item in walk(payloads):
        if isinstance(item, dict):
            keys.update(key for key, value in item.items() if isinstance(value, bool))
    return keys


def normalized(text: str) -> str:
    return text.replace("_", " ").replace("-", " ").lower()


def test_sprint161_expected_emitters_are_present() -> None:
    scripts = discover_sprint161_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES


def test_sprint161_emitters_write_artifacts_and_preserve_fail_closed_clay_flags(
    tmp_path: Path,
) -> None:
    scripts = discover_sprint161_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES

    combined_text = ""
    for script in scripts:
        payloads, text, artifact_paths = run_script(script, tmp_path / script.stem)
        combined_text += "\n" + script.name + "\n" + text

        assert payloads, [path.name for path in artifact_paths]
        assert any(item.get("sprint") == SPRINT for item in walk(payloads) if isinstance(item, dict)), text
        assert bool_values(payloads, "validation_passed"), text
        assert all(value is True for value in bool_values(payloads, "validation_passed")), script.name

        for key in boolean_keys(payloads):
            if key in FALSE_CLAY_AND_PROMOTION_FLAGS:
                assert all(value is False for value in bool_values(payloads, key)), (script.name, key)

    normalized_text = normalized(combined_text)
    for term in REQUIRED_TERMS:
        assert term in normalized_text
