from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_identifiability.py"

EXPECTED_QUERIES = ["waveform", "frequency", "amplitude", "phase", "hidden_state"]
FAIL_CLOSED_FLAGS = {
    "neuroscience_interpretation_promoted": False,
    "memory_mechanism_promoted": False,
    "hebbian_identity_promoted": False,
    "oja_identity_promoted": False,
    "kuramoto_identity_promoted": False,
    "cognitive_dissonance_identity_promoted": False,
    "empirical_brain_fit_promoted": False,
    "three_six_nine_superiority_promoted": False,
    "quantum_interpretation_promoted": False,
    "global_identifiability_promoted": False,
}


def run_identifiability(tmp_path: Path, *extra: str) -> dict:
    out_dir = tmp_path / "identifiability"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir), *extra],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    receipt_path = out_dir / "continuous_oscillator_identifiability.json"
    assert receipt_path.exists()
    assert json.loads(receipt_path.read_text(encoding="utf-8")) == payload
    return payload


def test_identifiability_runtime_declares_frozen_query_indexed_design(tmp_path: Path) -> None:
    payload = run_identifiability(
        tmp_path, "--seeds", "7", "17", "--max-steps", "120", "--samples", "256"
    )
    assert payload["diagnostic"] == "continuous_oscillator_identifiability"
    assert payload["status"] == "synthetic_identifiability_no_promotion"
    assert payload["parent_chain"] == {
        "structural_parent_pr": 896,
        "numerical_parent_pr": 909,
        "parent_following": True,
    }
    assert payload["oscillator_counts"] == [3, 6, 9]
    assert payload["query_family"] == EXPECTED_QUERIES
    assert payload["design"]["frequencies_learnable"] is True
    assert payload["design"]["frequency_bounds_hz"][0] < payload["design"]["frequency_bounds_hz"][1]
    assert 0.0 < payload["design"]["train_fraction"] < 1.0
    assert payload["design"]["frozen_before_holdout"] is True
    assert payload["design"]["observable_tolerance"] > 0.0
    assert payload["design"]["parameter_tolerance"] > 0.0
    assert payload["comparison_policy"] == {
        "same_target_support": True,
        "ranking_required": False,
        "nine_superiority_assumed": False,
        "query_adequacy_is_relative": True,
    }
    assert payload["promotion"]["state"] == "blocked"
    assert payload["promotion"]["flags"] == FAIL_CLOSED_FLAGS
    assert len(payload["runs"]) == 6
    for run in payload["runs"]:
        assert run["oscillator_count"] in {3, 6, 9}
        assert run["frequencies_learnable"] is True
        assert run["train_fit_loss"] >= 0.0
        assert run["heldout_fit_loss"] >= 0.0
        assert run["query_diagnostics"]["waveform"]["consumer"] == "heldout_reconstruction"
        assert run["query_diagnostics"]["frequency"]["consumer"] == "canonical_parameter_recovery"
        assert run["query_diagnostics"]["hidden_state"]["consumer"] == "canonical_hidden_state_recovery"


def test_recovery_is_gauge_normalized_and_near_collision_is_only_diagnostic(tmp_path: Path) -> None:
    payload = run_identifiability(
        tmp_path, "--seeds", "7", "17", "29", "--max-steps", "160", "--samples", "320"
    )
    assert payload["gauge_policy"] == {
        "phase_periodicity_mod_2pi": True,
        "permutation_within_target_group": True,
        "matching_rule": "nearest_target_frequency_then_frequency_order",
        "global_time_origin_quotiented": False,
        "amplitude_sign_phase_equivalence_quotiented": False,
    }
    assert payload["formal_boundary"]["numerical_near_collision_is_exact_nonfactorability_proof"] is False
    assert payload["near_collision_summary"]["status"] in {"observed", "not_observed"}
    for run in payload["runs"]:
        recovery = run["recovery"]
        assert recovery["gauge_normalized"] is True
        assert recovery["frequency_rmse_hz"] >= 0.0
        assert recovery["amplitude_rmse"] >= 0.0
        assert recovery["phase_rmse_rad"] >= 0.0
        assert recovery["canonical_parameter_distance"] >= 0.0
        assert run["near_collision_diagnostic"]["exact_nonfactorability_proved"] is False


def test_falsification_ladder_refits_and_keeps_null_axes_distinct(tmp_path: Path) -> None:
    payload = run_identifiability(
        tmp_path,
        "--seeds", "7", "17",
        "--max-steps", "100",
        "--samples", "240",
        "--null-steps", "45",
    )
    ladder = payload["falsification_ladder"]
    assert ladder["frozen_before_execution"] is True
    assert ladder["restart"]["refit_required"] is True
    assert ladder["noise"]["refit_required"] is True
    assert ladder["frequency_separation"]["refit_required"] is True
    assert ladder["spectral_transfer"]["refit_required"] is True
    assert ladder["gauge"]["refit_required"] is False
    assert ladder["gauge"]["semantic_identity_test"] is True
    assert ladder["noise"]["levels"] == [0.0, 0.02, 0.05]
    assert ladder["frequency_separation"]["factors"] == [1.0, 0.6, 0.3]
    assert ladder["spectral_transfer"]["offset_hz"] > 0.0
    assert set(ladder["by_count"]) == {"3", "6", "9"}
    for entry in ladder["by_count"].values():
        assert entry["restart_count"] >= 2
        assert entry["all_null_results_are_diagnostics"] is True
        assert entry["global_identifiability_proved"] is False


def test_pareto_ranking_is_eligible_only_and_never_promotes_truth(tmp_path: Path) -> None:
    payload = run_identifiability(
        tmp_path,
        "--seeds", "7", "17", "29",
        "--max-steps", "120",
        "--samples", "288",
        "--null-steps", "50",
    )
    pareto = payload["eligible_only_pareto"]
    assert pareto["selection_policy"] == "admissible_and_consumer_adequate_before_cost_ranking"
    assert pareto["lower_cost_implies_truth"] is False
    assert pareto["smaller_n_wins_by_definition"] is False
    assert pareto["larger_n_wins_by_definition"] is False
    assert pareto["axes"] == [
        "model_size",
        "heldout_error",
        "hidden_state_error",
        "restart_instability",
        "null_fragility",
    ]
    assert set(pareto["models"]) == {"3", "6", "9"}
    for model in pareto["models"].values():
        assert model["admissible"] is True
        assert model["consumer_adequate"] in {True, False}
        assert model["eligible"] == (model["admissible"] and model["consumer_adequate"])
        assert model["pareto_ranked"] == model["eligible"]
    assert set(pareto["frontier"]).issubset({"3", "6", "9"})
