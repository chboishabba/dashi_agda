from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc11_result_ledger.py"


def run_script(tmp_path: Path) -> tuple[dict[str, Any], str, Path]:
    if not SCRIPT.exists():
        pytest.skip(f"missing {SCRIPT}")

    output = tmp_path / "calc11_result_ledger.json"
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
    return file_payload, result.stdout + result.stderr, output


def test_calc11_result_ledger_emits_valid_deterministic_json(tmp_path: Path) -> None:
    payload, text, output = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_calc11_result_ledger"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True
    assert output.stat().st_size > 0

    control_card = payload["control_card"]
    assert set(control_card) == {
        "O",
        "R",
        "C",
        "S",
        "L",
        "P",
        "G",
        "F",
    }
    assert control_card["O"].startswith("Worker 2 owns the Calc 11 actual-result")
    assert control_card["F"] == "The ledger explicitly records no special alignment and no clay promotion."

    result = payload["result"]
    assert result["bottom_5_percent_g12_mean_omega_e2_fraction"] == 0.343
    assert result["random_baseline"] == 1.0 / 3.0
    assert result["full_boundary_layer_mean"] == 0.432
    assert result["max"] == 1.0
    assert result["max_omega_e2_fraction"] == 1.0
    assert result["percentile_distribution"] == "isolated/scattered across percentiles"
    assert result["monotone_increase_as_g12_decreases"] is False

    assert payload["decision"] == "no_special_alignment"
    assert payload["implications"]["special_alignment_supported"] is False
    assert payload["non_promotion"]["clay_promotion"] is False
    assert payload["parity_hash"]
    assert len(payload["parity_hash"]) == 64
    assert "no_special_alignment" in text
    assert "validation_passed" in json.dumps(payload, sort_keys=True)


def test_calc11_result_validator_rejects_tampered_payload() -> None:
    spec = importlib.util.spec_from_file_location("calc11_result_ledger", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    payload = module.build_payload()
    assert module.validate_payload(payload) is True

    tampered = json.loads(json.dumps(payload))
    tampered["result"]["bottom_5_percent_g12_mean_omega_e2_fraction"] = 0.344
    assert module.validate_payload(tampered) is False
