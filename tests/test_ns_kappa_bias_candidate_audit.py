from __future__ import annotations

import json
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_kappa_bias_candidate_audit.py"


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def bool_values_for_key(payload: Any, key_name: str) -> list[bool]:
    found: list[bool] = []
    for item in walk(payload):
        if isinstance(item, dict):
            for key, value in item.items():
                if key == key_name and isinstance(value, bool):
                    found.append(value)
    return found


def run_audit(tmp_path: Path) -> dict[str, Any]:
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(tmp_path / "audit"),
            "--markdown",
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    summary_path = tmp_path / "audit" / "ns_kappa_bias_candidate_audit_summary.json"
    report_path = tmp_path / "audit" / "ns_kappa_bias_candidate_audit.md"
    assert summary_path.is_file()
    assert report_path.is_file()
    assert json.loads(summary_path.read_text(encoding="utf-8")) == payload
    return payload


def test_kappa_bias_candidate_audit_records_core_identity_fields(tmp_path: Path) -> None:
    payload = run_audit(tmp_path)
    fields = payload["core_identity_fields"]

    assert payload["contract"] == "ns_kappa_bias_candidate_audit"
    assert payload["route_decision"] == "NS_C_KAPPA_BIAS_ROUTE_CANDIDATE_OPEN_NON_PROMOTING"
    assert payload["status"] == "candidate_open_non_promoting_not_proved"
    assert fields["gaussian_weight"] == "G(y)=exp(-|y|^2/4)"
    assert (
        fields["gaussian_self_similar_balance_identity"]
        == "2 int |grad omega|^2 G dy - 1/2 int |omega|^2 G dy = 4 Bias_G Omega_G + Drift_G Omega_G"
    )
    assert fields["ou_poincare_lower_bound"] == "int |grad omega|^2 G dy >= 1/2 int |omega|^2 G dy"
    assert fields["necessary_normalized_constraint"] == "1 <= 4 Bias_G + Drift_G"
    assert fields["drift_integration_by_parts_term"] == "Drift_G Omega_G"
    assert fields["bias_g_to_abel_integral_mapping"] == "Bias_G maps to int lambda(c)(kappa^2-1/2) dmu"
    assert fields["abel_integrand"] == "lambda(c)(kappa^2-1/2)"
    assert all(payload["structural_checks"].values())


def test_kappa_bias_candidate_audit_records_blockers_and_false_promotion_flags(tmp_path: Path) -> None:
    payload = run_audit(tmp_path)
    blocker_ids = set(payload["blocker_ids"])

    assert {
        "abel_triadic_defect_measure_construction",
        "bias_g_to_abel_integral_identification",
        "drift_integration_by_parts_control",
        "approximate_stationarity_under_t_ns",
        "compensated_leakage_identity",
        "local_defect_monotonicity_and_ckn_bkm_closure",
    } <= blocker_ids
    assert all(row["status"] == "OPEN_BLOCKER" for row in payload["blockers"])
    assert all(row["proved"] is False for row in payload["blockers"])

    flags = payload["promotion_flags"]
    assert flags["route_candidate"] is True
    assert flags["route_open"] is True
    assert flags["route_non_promoting"] is True
    false_flags = {
        key: value
        for key, value in flags.items()
        if key not in {"route_candidate", "route_open", "route_non_promoting"}
    }
    assert false_flags
    assert all(value is False for value in false_flags.values())
    assert bool_values_for_key(payload, "candidate_proved") == [False]
    assert bool_values_for_key(payload, "clay_navier_stokes_promoted") == [False]
    assert bool_values_for_key(payload, "promotion_allowed") == [False]
    assert payload["promotion"]["promotes_ns_clay"] is False
    assert payload["promotion"]["promotes_type_i_kappa_bias_bound"] is False
    assert payload["promotion"]["promotes_abel_measure_construction"] is False


def test_kappa_bias_candidate_audit_exposes_control_card(tmp_path: Path) -> None:
    payload = run_audit(tmp_path)
    card = payload["control_card"]

    assert set(card) == {"O", "R", "C", "S", "L", "P", "G", "F"}
    assert "open" in card["R"]
    assert "non-promoting" in card["R"]
    assert card["P"] == payload["route_decision"]
    assert "drift" in card["F"].lower()
