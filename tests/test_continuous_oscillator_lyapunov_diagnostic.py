from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_lyapunov_diagnostic.py"


def test_lyapunov_diagnostic_separates_sampled_descent_from_global_theorem(tmp_path: Path) -> None:
    out_dir = tmp_path / "lyapunov"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            "--seeds",
            "7",
            "17",
            "--steps",
            "80",
            "--samples",
            "256",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["diagnostic"] == "continuous_oscillator_lyapunov_diagnostic"
    assert payload["status"] == "finite_sample_descent_no_global_theorem"
    assert payload["oscillator_counts"] == [3, 6, 9]
    assert payload["candidate_laws"] == [
        "current_gradient",
        "hebbian_style_correlation",
        "oja",
        "kuramoto",
    ]
    assert payload["energy"]["name"] == "waveform_mse"
    assert payload["energy"]["semantic_truth_metric"] is False
    assert payload["energy"]["natural_lyapunov_for_all_candidates"] is False
    assert payload["policy"]["same_energy_used_for_comparison"] is True
    assert payload["policy"]["candidate_native_energy_claimed"] is False
    assert payload["policy"]["sampled_nonincrease_is_global_lyapunov_theorem"] is False

    assert len(payload["runs"]) == 6
    for run in payload["runs"]:
        assert run["oscillator_count"] in {3, 6, 9}
        for name in payload["candidate_laws"]:
            candidate = run["candidates"][name]
            assert candidate["steps_observed"] == 80
            assert 0 <= candidate["nonincrease_steps"] <= 80
            assert 0.0 <= candidate["nonincrease_fraction"] <= 1.0
            assert candidate["initial_energy"] >= 0.0
            assert candidate["final_energy"] >= 0.0
            assert candidate["global_lyapunov_proved"] is False
            assert candidate["empirical_mechanism_identity_proved"] is False

    assert payload["promotion"]["objective_descent_implies_truth"] is False
    assert payload["promotion"]["sampled_descent_implies_memory_mechanism"] is False
    assert payload["promotion"]["three_six_nine_stability_ordering"] is False

    receipt = out_dir / "continuous_oscillator_lyapunov_diagnostic.json"
    assert receipt.exists()
    assert json.loads(receipt.read_text(encoding="utf-8")) == payload
