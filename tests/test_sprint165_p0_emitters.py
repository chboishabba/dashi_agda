from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
GENERATED_AT = "1970-01-01T00:00:00Z"

EXPECTED_SCRIPT_NAMES = {
    "p0_clay_finite_hodge_ns_stack.py",
    "ns_clay_microlocal_gap_chain.py",
    "finite_hodge_variation_gap_chain.py",
}

REQUIRED_NEXT_PROOF_NAMES = {
    "BTFiniteHodgeVariationTheorem",
    "AngularDegeneracyPressureCommutatorGain",
}

FALSE_PROMOTION_FLAGS = {
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
    "continuum_ym_mass_gap_promoted",
    "continuumYMMassGapPromoted",
    "clay_yang_mills_promoted",
    "yang_mills_clay_promoted",
    "standard_model_promoted",
    "terminal_unification_promoted",
}


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def discover_scripts() -> list[Path]:
    return sorted(SCRIPT_DIR / name for name in EXPECTED_SCRIPT_NAMES if (SCRIPT_DIR / name).is_file())


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def artifact_text(paths: list[Path]) -> str:
    parts: list[str] = []
    for path in paths:
        if path.suffix.lower() in {".json", ".csv", ".md"}:
            parts.append(path.read_text(encoding="utf-8", errors="replace"))
    return "\n".join(parts)


def run_script(script: Path, out_dir: Path) -> tuple[list[Any], list[Path], str]:
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
    text = "\n".join([result.stdout, result.stderr, artifact_text(artifact_paths)])

    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
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
    assert all(path.stat().st_size > 0 for path in artifact_paths), [path.name for path in artifact_paths]
    assert all(path.stat().st_size > 0 for path in artifact_paths if path.suffix.lower() in {".csv", ".md"})

    payloads = [load_json(path) for path in artifact_paths if path.suffix.lower() == ".json"]
    return payloads, artifact_paths, text


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


def normalize_key(key: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", key.lower()).strip("_")


def is_promotion_flag(key: str) -> bool:
    normalized = normalize_key(key)
    compact = normalized.replace("_", "")
    if "fail_closed" in normalized or normalized.endswith("_recorded") or "recorded" in normalized:
        return False
    if key in FALSE_PROMOTION_FLAGS or compact in {normalize_key(flag).replace("_", "") for flag in FALSE_PROMOTION_FLAGS}:
        return True
    if "promotion" in normalized or "promoted" in normalized or normalized.startswith("can_promote"):
        return True
    if "clay" in normalized:
        return any(
            marker in normalized
            for marker in {
                "solved",
                "promoted",
                "promotion",
                "submission",
                "mechanism",
                "exhaustion",
                "theorem",
                "ready",
            }
        )
    return any(marker in normalized for marker in {"terminal_unification", "continuum_mass_gap"})


def manifest_payloads(payloads: list[Any]) -> list[dict[str, Any]]:
    manifests: list[dict[str, Any]] = []
    for payload in payloads:
        if isinstance(payload, dict) and (
            "manifest_hash" in payload
            or "files" in payload
            or "artifacts" in payload
            or "artifact_count" in payload
        ):
            manifests.append(payload)
    return manifests


def file_entries(value: Any) -> Iterable[dict[str, Any]]:
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        keys = {str(key).lower() for key in item}
        if keys & {"sha256", "checksum", "digest"} and keys & {"name", "path", "file", "filename"}:
            yield item


def entry_name(entry: dict[str, Any]) -> str | None:
    for key in ("name", "file", "filename", "path"):
        value = entry.get(key)
        if isinstance(value, str) and value:
            return Path(value).name
    return None


def entry_sha256(entry: dict[str, Any]) -> str | None:
    for key, value in entry.items():
        if isinstance(value, str) and "sha256" in str(key).lower():
            return value.removeprefix("sha256:")
    for key in ("checksum", "digest"):
        value = entry.get(key)
        if isinstance(value, str) and re.fullmatch(r"(?:sha256:)?[0-9a-fA-F]{64}", value):
            return value.removeprefix("sha256:")
    return None


def assert_manifest_checksums_match(payloads: list[Any], artifact_paths: list[Path]) -> None:
    artifacts_by_name = {path.name: path for path in artifact_paths}
    manifests = manifest_payloads(payloads)
    assert manifests, [path.name for path in artifact_paths]

    checked: list[str] = []
    for manifest in manifests:
        for entry in file_entries(manifest):
            name = entry_name(entry)
            expected = entry_sha256(entry)
            if not name or not expected:
                continue
            if name.endswith("_manifest.json"):
                continue
            if name not in artifacts_by_name:
                continue
            actual = hashlib.sha256(artifacts_by_name[name].read_bytes()).hexdigest()
            assert actual == expected.lower(), (name, expected, actual)
            checked.append(name)

    non_manifest_artifacts = {path.name for path in artifact_paths if not path.name.endswith("_manifest.json")}
    assert non_manifest_artifacts <= set(checked), (sorted(non_manifest_artifacts), sorted(checked))


def test_sprint165_expected_p0_emitters_are_present() -> None:
    scripts = discover_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES


def test_sprint165_p0_emitters_write_deterministic_fail_closed_artifacts(tmp_path: Path) -> None:
    scripts = discover_scripts()
    assert {path.name for path in scripts} == EXPECTED_SCRIPT_NAMES

    scratch_dir = OUTPUTS_DIR / ".pytest_sprint165_p0_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)

    combined_text = ""
    try:
        for script in scripts:
            payloads, artifact_paths, text = run_script(script, scratch_dir / script.stem)
            combined_text += "\n" + script.name + "\n" + text

            assert payloads, [path.name for path in artifact_paths]

            validation_values = bool_values(payloads, "validation_passed")
            if validation_values:
                assert all(value is True for value in validation_values), script.name

            generated_at_values = string_values(payloads, "generated_at")
            assert generated_at_values, text
            assert set(generated_at_values) == {GENERATED_AT}, (script.name, generated_at_values)

            for key in boolean_keys(payloads):
                if is_promotion_flag(key):
                    assert all(value is False for value in bool_values(payloads, key)), (script.name, key)

            assert_manifest_checksums_match(payloads, artifact_paths)
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    for name in REQUIRED_NEXT_PROOF_NAMES:
        assert name in combined_text, name
