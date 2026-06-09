from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
SPRINT = 163
GENERATED_AT = "1970-01-01T00:00:00Z"

EXPECTED_SCRIPT_NAMES = {
    "ns_sprint163_sanni_symbol_obstruction_source.py",
    "ns_sprint163_critical_alignment_topological_exhaustion_target.py",
    "ns_sprint163_sigma_local_analysis_gap.py",
}

REQUIRED_NAMES = {
    "TopologicalAlignmentObstruction",
    "CriticalAlignmentTopologicalExhaustion",
    "SigmaLocalAnalysis",
}

FALSE_CLAY_AND_PDE_PROMOTION_FLAGS = {
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
    "ClayNavierStokesPromoted",
    "clay_promotion_allowed",
    "clayPromotionAllowed",
    "promotion_allowed",
    "promotionAllowed",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
    "full_unification_promoted",
    "fullUnificationPromoted",
    "full_clay_ns_promoted",
    "fullClayNSPromoted",
    "pde_promotion_allowed",
    "pdePromotionAllowed",
    "PDEPromotionAllowed",
    "new_pde_math_promoted",
    "newPDEMathPromoted",
    "PDEClosurePromoted",
    "pde_closure_promoted",
}


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def discover_sprint163_scripts() -> list[Path]:
    return sorted(
        path
        for path in SCRIPT_DIR.glob("ns_sprint163_*.py")
        if path.is_file() and path.name in EXPECTED_SCRIPT_NAMES
    )


def run_script(script: Path, out_dir: Path) -> tuple[list[Any], str, list[Path]]:
    result = subprocess.run(
        [
            sys.executable,
            str(script),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
            "--generated-at",
            GENERATED_AT,
        ],
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
    assert any(path.name.endswith("_rows.json") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.name.endswith("_rows.csv") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.name.endswith("_manifest.json") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.suffix.lower() == ".md" for path in artifact_paths), [
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


def string_values(payloads: list[Any], key: str) -> list[str]:
    values: list[str] = []
    for item in walk(payloads):
        if isinstance(item, dict) and isinstance(item.get(key), str):
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


def is_clay_or_pde_promotion_flag(key: str) -> bool:
    normalized_key = normalized(key)
    if key in FALSE_CLAY_AND_PDE_PROMOTION_FLAGS:
        return True
    if "clay" in normalized_key:
        return True
    if "promotion" in normalized_key or "promoted" in normalized_key:
        return True
    return "pde" in normalized_key and any(
        marker in normalized_key for marker in {"closure", "promotion", "promoted", "solved"}
    )


def test_sprint163_expected_emitters_are_present() -> None:
    scripts = discover_sprint163_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES


def test_sprint163_emitters_write_validated_deterministic_artifacts_and_hold_promotion(
    tmp_path: Path,
) -> None:
    scripts = discover_sprint163_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES

    combined_text = ""
    for script in scripts:
        payloads, text, artifact_paths = run_script(script, tmp_path / script.stem)
        combined_text += "\n" + script.name + "\n" + text

        assert payloads, [path.name for path in artifact_paths]
        assert any(item.get("sprint") == SPRINT for item in walk(payloads) if isinstance(item, dict)), text

        validation_values = bool_values(payloads, "validation_passed")
        assert validation_values, text
        assert all(value is True for value in validation_values), script.name

        generated_at_values = string_values(payloads, "generated_at")
        assert generated_at_values, text
        assert set(generated_at_values) == {GENERATED_AT}, (script.name, generated_at_values)

        for key in boolean_keys(payloads):
            if is_clay_or_pde_promotion_flag(key):
                assert all(value is False for value in bool_values(payloads, key)), (script.name, key)

    normalized_text = normalized(combined_text)
    for name in REQUIRED_NAMES:
        assert normalized(name) in normalized_text, name
