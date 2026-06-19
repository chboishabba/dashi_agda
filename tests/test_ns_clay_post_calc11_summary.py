from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_post_calc11_summary.py"


def run_script(tmp_path: Path) -> tuple[dict[str, Any], str]:
    if not SCRIPT.exists():
        raise AssertionError(f"missing {SCRIPT}")

    output = tmp_path / "ns_clay_post_calc11_summary.json"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--output",
            str(output),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert output.exists()

    stdout_payload = json.loads(result.stdout)
    file_payload = json.loads(output.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    return file_payload, result.stdout


def test_post_calc11_summary_ledger_emits_deterministic_json(tmp_path: Path) -> None:
    payload, text = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_post_calc11_summary"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True
    assert payload["calc11_complete"] is True
    assert payload["calc11_decision"] == "no_special_alignment"
    assert payload["no_further_calcs_blocking"] is True
    assert payload["closeable_package_count"] == 7
    assert payload["closeable_packages"] == [
        "millerToH5",
        "GD3-SobolevBound-Correct",
        "coareaGradientBound",
        "LocalConcentration",
        "pigeon_concentration",
        "StepA_PerComponent",
        "BoundaryHB_Correct",
    ]
    assert payload["remaining_hard_walls"] == ["KornLevelSet", "collapseImpossible"]
    assert payload["hard_wall_count"] == 2
    assert payload["clay_hard_core"] == "collapseImpossible"
    assert payload["optional_next_calc"] == "Calc12:parametric_omega_e2_scaling_study"
    assert payload["optional_next_calc_blocks_proof"] is False
    assert payload["clay_promotion"] is False
    assert payload["theorem_promotion"] is False
    assert isinstance(payload["parity_hash"], str) and len(payload["parity_hash"]) == 64
    assert payload["parity_hash"] in text


def test_post_calc11_summary_validator_rejects_tampering_and_hash_changes() -> None:
    spec = importlib.util.spec_from_file_location("post_calc11_summary", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    payload = module.build_payload()
    assert module.validate_payload(payload) is True

    tampered = json.loads(json.dumps(payload))
    tampered["closeable_packages"][0] = "wrong_package"
    assert module.validate_payload(tampered) is False

    tampered_hash = json.loads(json.dumps(payload))
    tampered_hash["parity_hash"] = "0" * 64
    assert module.validate_payload(tampered_hash) is False
