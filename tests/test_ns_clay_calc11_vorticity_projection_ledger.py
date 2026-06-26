from __future__ import annotations

import json
import importlib.util
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc11_vorticity_projection_ledger.py"


def run_script(tmp_path: Path) -> tuple[dict[str, Any], str, Path]:
    if not SCRIPT.exists():
        pytest.skip(f"missing {SCRIPT}")

    output = tmp_path / "calc11_vorticity_projection_ledger.json"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--json-output",
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
    return file_payload, result.stdout + result.stderr, output


def test_calc11_vorticity_projection_ledger_emits_valid_deterministic_json(
    tmp_path: Path,
) -> None:
    payload, text, output = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_calc11_vorticity_projection_ledger"
    assert payload["calc_id"] == 11
    assert payload["calc_name"] == "vorticity_e2_projection_boundary_layer"
    assert payload["validation_passed"] is True
    assert output.stat().st_size > 0

    required_inputs = payload["required_inputs"]
    assert [item["name"] for item in required_inputs] == [
        "velocity_field",
        "vorticity_field",
        "strain_eigenframe",
        "boundary_layer_mask",
        "gap_field",
    ]
    assert all(item["required"] is True for item in required_inputs)

    formula = payload["formula"]
    assert "|<omega,e2>|^2" in formula["expression"]
    assert formula["symbols"]["e2"].startswith("middle strain eigenvector")
    assert formula["symbols"]["eps"] == "positive tolerance floor"

    thresholds = payload["decision_thresholds"]
    assert thresholds["omega_e2_fraction_low"] == 0.1
    assert thresholds["omega_e2_fraction_random"] == 1.0 / 3.0
    assert thresholds["omega_e2_fraction_high"] == 0.9
    assert thresholds["promotion_margin_min"] == 1.0
    assert thresholds["non_promotion_required"] is True

    assert [item["name"] for item in payload["output_fields"]] == [
        "mean_omega_e2_fraction",
        "max_omega_e2_fraction",
        "layer_cell_count",
        "min_g12",
    ]

    non_promotion_flags = payload["non_promotion_flags"]
    assert set(non_promotion_flags) == {
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "full_clay_ns_solved",
        "fullClayNSSolved",
        "promotion_allowed",
        "proof_claimed",
    }
    assert all(flag is False for flag in non_promotion_flags.values())
    assert "vorticity" in text.lower()
    assert "non_promotion_required" in json.dumps(payload, sort_keys=True)


def test_calc11_validator_rejects_tampered_payload() -> None:
    spec = importlib.util.spec_from_file_location("calc11_ledger", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    payload = module.build_payload()
    assert module.validate_payload(payload) is True

    tampered = json.loads(json.dumps(payload))
    tampered["non_promotion_flags"]["clay_navier_stokes_promoted"] = True
    assert module.validate_payload(tampered) is False
