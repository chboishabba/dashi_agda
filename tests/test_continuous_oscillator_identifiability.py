from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_identifiability.py"

EXPECTED_QUERIES = [
    "waveform",
    "frequency",
    "amplitude",
    "phase",
    "hidden_state",
]

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


def test_identifiability_runtime_declares_frozen_query_indexed_design(tmp_path: Path) -> None:
    out_dir = tmp_path / "identifiability"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            "--seeds",
            "7",
            "17",
            "--max-steps",
            "120",
            "--samples",
            "256",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)

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

    receipt_path = out_dir / "continuous_oscillator_identifiability.json"
    assert receipt_path.exists()
    assert json.loads(receipt_path.read_text(encoding="utf-8")) == payload
