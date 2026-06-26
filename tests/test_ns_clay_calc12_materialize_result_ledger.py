from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc12_materialize_result_ledger.py"
DEFAULT_INPUT = REPO_ROOT / "scripts" / "data" / "outputs" / "ns_clay_calc12_route_selector_real_N128_20260619.json"


def run_script(tmp_path: Path) -> tuple[dict[str, Any], str, Path]:
    assert SCRIPT.exists(), f"missing {SCRIPT}"

    input_path = tmp_path / "ns_clay_calc12_route_selector_real_N128_20260619.json"
    input_path.write_text(DEFAULT_INPUT.read_text(encoding="utf-8"), encoding="utf-8")

    output = tmp_path / "ns_clay_calc12_result_ledger_real_N128_20260619.json"
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(input_path), "--output", str(output)],
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
    return file_payload, result.stdout, output


def test_ns_clay_calc12_materialize_result_ledger_emits_deterministic_json(tmp_path: Path) -> None:
    payload, text, output = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_calc12_result_ledger"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True
    assert payload["input"].endswith("ns_clay_calc12_route_selector_real_N128_20260619.json")
    assert payload["proof_blocking"] is False
    assert payload["theorem_authority"] is False
    assert payload["clay_promotion"] is False
    assert output.stat().st_size > 0

    control_card = payload["control_card"]
    assert set(control_card) == {"O", "R", "C", "S", "L", "P", "G", "F"}
    assert control_card["F"] == (
        "The ledger explicitly records proof_blocking False, theorem_authority False, and clay_promotion False."
    )

    result = payload["result"]
    assert set(result) == {"aggregate_decision", "beta", "ci", "n_pairs_used", "r_squared"}
    assert result["aggregate_decision"] == "regularity_consistent"
    assert result["beta"] == 2.2754974180523737
    assert result["ci"] == [2.129779448947756, 2.4212153871569915]
    assert result["r_squared"] == 0.13893110418597066
    assert result["n_pairs_used"] == 5808
    assert json.loads(text) == payload

    second_output = tmp_path / "ns_clay_calc12_result_ledger_real_N128_20260619_second.json"
    second = subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(tmp_path / "ns_clay_calc12_route_selector_real_N128_20260619.json"), "--output", str(second_output)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert second.returncode == 0, second.stdout + second.stderr
    assert json.loads(second.stdout) == payload
    assert second_output.read_text(encoding="utf-8") == output.read_text(encoding="utf-8")


def test_ns_clay_calc12_materializer_module_imports_and_rejects_tampering() -> None:
    spec = importlib.util.spec_from_file_location("ns_clay_calc12_materialize_result_ledger", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    payload = module.build_payload(module.read_json(module.DEFAULT_INPUT), input_path=module.DEFAULT_INPUT)
    assert module.validate_payload({**payload, "validation_passed": True}) is True

    tampered = json.loads(json.dumps(payload))
    tampered["proof_blocking"] = True
    assert module.validate_payload(tampered) is False
