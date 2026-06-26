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
    expected_calc12 = {
        "calc": "Calc12",
        "route_selector": "statistical",
        "script": "scripts/ns_clay_calc12_route_selector.py",
        "pair_builder_script": "scripts/ns_clay_calc12_pair_builder.py",
        "expected_real_run_artifact": (
            "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
        ),
        "power_law": "|<omega,e2>|^2 ~ C*g12^beta",
        "fitted_beta": "candidate-only fitted beta placeholder",
        "fitted_C": "candidate-only fitted C placeholder",
        "beta_CI_95": "95% CI placeholder; compare the interval to 1 for route selection",
        "r_squared": "candidate-only r_squared placeholder",
        "n_pairs_raw": 9,
        "n_pairs_used": 9,
        "min_g12_observed": "candidate-only minimum observed g12 placeholder",
        "decision": "inconclusive",
        "aggregate_decision": "inconclusive",
        "beta_decision_thresholds": {
            ">1": "regularity_consistent",
            "<1": "blowup_precursor",
            "CI straddles 1": "inconclusive",
        },
        "proof_blocking": False,
        "no_further_calcs_blocking": True,
    }
    expected_calc12_result_summary = {
        "source_artifact": (
            "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
        ),
        "calc": "Calc12",
        "route_selector": "statistical",
        "beta": 2.2754974180523737,
        "beta_CI_95": [2.129779448947756, 2.4212153871569915],
        "delta_target": 1.0,
        "delta_empirical": 1.2754974180523737,
        "r_squared": 0.13893110418597066,
        "decision": "regularity_consistent",
        "aggregate_decision": "regularity_consistent",
        "fit_caveat": (
            "low rSquared caveat: this candidate route is recorded, but fit quality "
            "remains limited and should not be read as a theorem."
        ),
        "proof_blocking": False,
        "calculation_authority": False,
        "clay_promotion": False,
        "theorem_promotion": False,
    }

    assert payload["contract"] == "ns_clay_post_calc11_summary"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True
    assert payload["calc11_complete"] is True
    assert payload["calc11_decision"] == "no_special_alignment"
    assert payload["no_further_calcs_blocking"] is True
    assert payload["proof_blocking"] is False
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
    assert payload["optional_next_calc"] == expected_calc12
    assert payload["calc12_route_selector"] == expected_calc12
    assert payload["calc12_result_summary"] == expected_calc12_result_summary
    assert payload["optional_next_calc_blocks_proof"] is False
    assert payload["calc12_executable"] is True
    assert payload["calc12_pair_builder_script"] == "scripts/ns_clay_calc12_pair_builder.py"
    assert (
        payload["calc12_expected_real_run_artifact"]
        == "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    )
    assert payload["clay_promotion"] is False
    assert payload["theorem_promotion"] is False
    assert payload["calculation_authority"] is False
    assert payload["calc12_result_summary"]["source_artifact"] == (
        "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    )
    assert payload["calc12_result_summary"]["beta"] == 2.2754974180523737
    assert payload["calc12_result_summary"]["beta_CI_95"] == [
        2.129779448947756,
        2.4212153871569915,
    ]
    assert payload["calc12_result_summary"]["delta_target"] == 1.0
    assert payload["calc12_result_summary"]["delta_empirical"] == 1.2754974180523737
    assert payload["calc12_result_summary"]["r_squared"] == 0.13893110418597066
    assert payload["calc12_result_summary"]["decision"] == "regularity_consistent"
    assert payload["calc12_result_summary"]["aggregate_decision"] == "regularity_consistent"
    assert (
        payload["calc12_result_summary"]["fit_caveat"]
        == "low rSquared caveat: this candidate route is recorded, but fit quality remains limited and should not be read as a theorem."
    )
    assert payload["calc12_result_summary"]["proof_blocking"] is False
    assert payload["calc12_result_summary"]["calculation_authority"] is False
    assert payload["calc12_result_summary"]["clay_promotion"] is False
    assert payload["calc12_result_summary"]["theorem_promotion"] is False
    assert payload["calc12_route_selector"]["script"] == "scripts/ns_clay_calc12_route_selector.py"
    assert (
        payload["calc12_route_selector"]["pair_builder_script"]
        == "scripts/ns_clay_calc12_pair_builder.py"
    )
    assert (
        payload["calc12_route_selector"]["expected_real_run_artifact"]
        == "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    )
    assert payload["calc12_route_selector"]["fitted_beta"] == "candidate-only fitted beta placeholder"
    assert payload["calc12_route_selector"]["fitted_C"] == "candidate-only fitted C placeholder"
    assert (
        payload["calc12_route_selector"]["beta_CI_95"]
        == "95% CI placeholder; compare the interval to 1 for route selection"
    )
    assert payload["calc12_route_selector"]["r_squared"] == "candidate-only r_squared placeholder"
    assert payload["calc12_route_selector"]["n_pairs_raw"] == 9
    assert payload["calc12_route_selector"]["n_pairs_used"] == 9
    assert (
        payload["calc12_route_selector"]["min_g12_observed"]
        == "candidate-only minimum observed g12 placeholder"
    )
    assert payload["calc12_route_selector"]["decision"] == "inconclusive"
    assert payload["calc12_route_selector"]["aggregate_decision"] == "inconclusive"
    assert isinstance(payload["parity_hash"], str) and len(payload["parity_hash"]) == 64
    assert payload["parity_hash"] in text
    assert payload["control_card"]["calc12_route_selector"] == expected_calc12
    assert payload["control_card"]["optional_next_calc_blocks_proof"] is False
    assert payload["control_card"]["calc12_executable"] is True
    assert payload["control_card"]["calc12_pair_builder_script"] == "scripts/ns_clay_calc12_pair_builder.py"
    assert (
        payload["control_card"]["calc12_expected_real_run_artifact"]
        == "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    )
    assert payload["control_card"]["calc12_result_summary"] == expected_calc12_result_summary
    assert payload["control_card"]["proof_blocking"] is False
    assert payload["control_card"]["calculation_authority"] is False
    assert payload["control_card"]["no_further_calcs_blocking"] is True


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

    tampered_calc12 = json.loads(json.dumps(payload))
    tampered_calc12["calc12_expected_real_run_artifact"] = "scripts/data/outputs/wrong.json"
    assert module.validate_payload(tampered_calc12) is False

    tampered_result_summary = json.loads(json.dumps(payload))
    tampered_result_summary["calc12_result_summary"]["aggregate_decision"] = "inconclusive"
    assert module.validate_payload(tampered_result_summary) is False

    tampered_delta = json.loads(json.dumps(payload))
    tampered_delta["calc12_result_summary"]["delta_empirical"] = 0.0
    assert module.validate_payload(tampered_delta) is False

    tampered_caveat = json.loads(json.dumps(payload))
    tampered_caveat["calc12_result_summary"]["fit_caveat"] = "changed"
    assert module.validate_payload(tampered_caveat) is False

    tampered_flag = json.loads(json.dumps(payload))
    tampered_flag["calculation_authority"] = True
    assert module.validate_payload(tampered_flag) is False
