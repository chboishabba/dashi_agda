from __future__ import annotations

import importlib.util
import json
import math
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc12_result_ledger.py"
DEFAULT_INPUT = Path("scripts") / "data" / "outputs" / "ns_clay_calc12_route_selector_real_N128_20260619.json"


def run_script(tmp_path: Path) -> tuple[dict[str, Any], str, Path]:
    if not SCRIPT.exists():
        raise AssertionError(f"missing {SCRIPT}")

    output = tmp_path / "ns_clay_calc12_result_ledger.json"
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--output", str(output)],
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


def load_module():
    spec = importlib.util.spec_from_file_location("ns_clay_calc12_result_ledger", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def clone_json(value: Any) -> Any:
    return json.loads(json.dumps(value))


def mutate_path(payload: Any, path: tuple[Any, ...], value: Any) -> None:
    cursor = payload
    for step in path[:-1]:
        cursor = cursor[step]
    cursor[path[-1]] = value


def test_calc12_result_ledger_emits_deterministic_json(tmp_path: Path) -> None:
    payload, text, output = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_calc12_result_ledger"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True
    assert payload["input"] == str(DEFAULT_INPUT)
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
    assert result["aggregate_decision"] == "regularity_consistent"
    assert result["beta"] == 2.2754974180523737
    assert result["ci"] == [2.129779448947756, 2.4212153871569915]
    assert result["r_squared"] == 0.13893110418597066
    assert result["n_pairs_used"] == 5808
    assert json.loads(text) == payload


@pytest.mark.parametrize(
    ("path", "value", "message_fragment"),
    [
        (("datasets", 0, "fit", "beta"), math.nan, "beta must be finite"),
        (("datasets", 0, "fit", "beta_CI_95", 0), math.inf, "beta_CI_95[0] must be finite"),
        (("datasets", 0, "fit", "beta_CI_95", 1), -math.inf, "beta_CI_95[1] must be finite"),
        (("datasets", 0, "fit", "r_squared"), math.nan, "r_squared must be finite"),
        (("datasets", 0, "fit", "fitted_C"), math.inf, "fitted_C must be finite"),
        (("datasets", 0, "fit", "log_C"), -math.inf, "log_C must be finite"),
        (("datasets", 0, "fit", "standard_error_beta"), math.nan, "standard_error_beta must be finite"),
        (("datasets", 0, "fit", "intercept"), math.inf, "intercept must be finite"),
        (("datasets", 0, "fit", "delta_target"), math.nan, "delta_target must be finite"),
        (("datasets", 0, "min_g12_observed"), math.nan, "min_g12_observed must be finite"),
        (("datasets", 0, "max_g12_observed"), math.inf, "max_g12_observed must be finite"),
        (("datasets", 0, "n_pairs_raw"), math.nan, "n_pairs_raw must be a positive integer"),
        (("datasets", 0, "n_pairs_used"), math.inf, "n_pairs_used must be a positive integer"),
        (("datasets", 0, "n_pairs"), -math.inf, "n_pairs must be a positive integer"),
    ],
)
def test_calc12_result_ledger_rejects_non_finite_json_payloads(
    tmp_path: Path, path: tuple[Any, ...], value: Any, message_fragment: str
) -> None:
    module = load_module()
    selector_payload = clone_json(module.read_json(module.DEFAULT_INPUT))
    mutate_path(selector_payload, path, value)

    input_path = tmp_path / "selector.json"
    input_path.write_text(json.dumps(selector_payload, indent=2, sort_keys=True), encoding="utf-8")

    output = tmp_path / "ledger.json"
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--input", str(input_path), "--output", str(output)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert result.returncode != 0
    assert message_fragment in result.stderr
    assert not output.exists()


@pytest.mark.parametrize(
    ("path", "value", "message_fragment"),
    [
        (("datasets", 0, "fit", "beta"), float("nan"), "beta must be finite"),
        (("datasets", 0, "fit", "beta_CI_95", 0), float("inf"), "beta_CI_95[0] must be finite"),
        (("datasets", 0, "fit", "r_squared"), float("-inf"), "r_squared must be finite"),
        (("datasets", 0, "fit", "fitted_C"), float("nan"), "fitted_C must be finite"),
        (("datasets", 0, "fit", "intercept"), float("inf"), "intercept must be finite"),
        (("datasets", 0, "fit", "delta_target"), float("-inf"), "delta_target must be finite"),
        (("datasets", 0, "max_g12_observed"), float("-inf"), "max_g12_observed must be finite"),
    ],
)
def test_calc12_result_ledger_rejects_parsed_non_finite_values(
    path: tuple[Any, ...], value: Any, message_fragment: str
) -> None:
    module = load_module()
    selector_payload = module.read_json(module.DEFAULT_INPUT)
    selector_payload = clone_json(selector_payload)
    mutate_path(selector_payload, path, value)

    with pytest.raises(module.InputError, match=re.escape(message_fragment)):
        module.validate_input_payload(selector_payload)


def test_calc12_result_ledger_accepts_route_selector_calibration_fields() -> None:
    module = load_module()
    selector_payload = clone_json(module.read_json(module.DEFAULT_INPUT))
    selector_payload["datasets"][0]["fit"]["delta_target"] = 1.2754974180523737
    selector_payload["datasets"][0]["fit"]["r_squared_caveat"] = "noisy_low_fit"

    module.validate_input_payload(selector_payload)
    payload = module.build_payload(selector_payload, input_path=module.DEFAULT_INPUT)
    assert payload["result"]["aggregate_decision"] == "regularity_consistent"


def test_calc12_result_ledger_rejects_unknown_route_selector_caveat() -> None:
    module = load_module()
    selector_payload = clone_json(module.read_json(module.DEFAULT_INPUT))
    selector_payload["datasets"][0]["fit"]["r_squared_caveat"] = "promoted"

    with pytest.raises(module.InputError, match="r_squared_caveat must be null or noisy_low_fit"):
        module.validate_input_payload(selector_payload)


def test_calc12_result_validator_rejects_promoted_payload() -> None:
    module = load_module()

    payload = module.build_payload(module.read_json(module.DEFAULT_INPUT), input_path=module.DEFAULT_INPUT)
    assert module.validate_payload({**payload, "validation_passed": True}) is True

    tampered = json.loads(json.dumps(payload))
    tampered["clay_promotion"] = True
    assert module.validate_payload(tampered) is False
