from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_synthetic.py"
OUTPUT_STEM = "continuous_oscillator_synthetic"
RECEIPT = ROOT / "DASHI" / "Cognition" / "PNF" / "ContinuousOscillatorSyntheticReceipt.agda"
AGGREGATE = ROOT / "DASHI" / "Cognition" / "PNF" / "PNFIRLearningEverything.agda"

FAIL_CLOSED_FLAGS = {
    "neuroscience_interpretation_promoted": False,
    "memory_mechanism_promoted": False,
    "hebbian_identity_promoted": False,
    "kuramoto_identity_promoted": False,
    "cognitive_dissonance_identity_promoted": False,
    "empirical_brain_fit_promoted": False,
    "three_six_nine_superiority_promoted": False,
    "quantum_interpretation_promoted": False,
}


def run_diagnostic(
    tmp_path: Path, *extra_args: str, leaf: str = "oscillator"
) -> tuple[dict[str, Any], Path]:
    out_dir = tmp_path / leaf
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            *extra_args,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    file_payload = json.loads(
        (out_dir / f"{OUTPUT_STEM}.json").read_text(encoding="utf-8")
    )
    assert payload == file_payload
    return payload, out_dir


def test_default_run_writes_receipt_artifacts_and_declares_369_conditions(
    tmp_path: Path,
) -> None:
    payload, out_dir = run_diagnostic(tmp_path)

    expected_paths = {
        "json": out_dir / f"{OUTPUT_STEM}.json",
        "trajectories_csv": out_dir / "continuous_oscillator_trajectories.csv",
        "comparison_csv": out_dir / "continuous_oscillator_comparison.csv",
        "markdown": out_dir / f"{OUTPUT_STEM}.md",
    }
    for path in expected_paths.values():
        assert path.exists()

    assert payload["diagnostic"] == OUTPUT_STEM
    assert payload["status"] == "synthetic_only_no_promotion"
    assert payload["oscillator_counts"] == [3, 6, 9]
    assert payload["promotion"]["state"] == "blocked"
    assert payload["promotion"]["flags"] == FAIL_CLOSED_FLAGS
    assert payload["output_paths"] == {
        key: str(path) for key, path in expected_paths.items()
    }

    with expected_paths["comparison_csv"].open(newline="", encoding="utf-8") as handle:
        comparison_rows = list(csv.DictReader(handle))
    assert len(comparison_rows) == len(payload["runs"])


def test_default_runs_share_target_support_keep_frequencies_fixed_and_reduce_fit_loss(
    tmp_path: Path,
) -> None:
    payload, _out_dir = run_diagnostic(tmp_path)

    target_frequencies = payload["target"]["frequencies_hz"]
    assert len(target_frequencies) == 3
    assert payload["default_seeds"] == [7, 17, 29]
    assert len(payload["runs"]) == 9

    for run in payload["runs"]:
        n = run["oscillator_count"]
        repeats = n // 3
        assert run["frequencies_fixed"] is True
        assert run["frequencies_hz"] == [
            frequency
            for frequency in target_frequencies
            for _ in range(repeats)
        ]
        assert run["final_fit_loss"] < run["initial_fit_loss"]
        assert run["loss_reduction_ratio"] > 0.0
        assert math.isfinite(run["final_total_objective"])
        assert math.isfinite(run["gradient_norm"])
        assert math.isfinite(run["parameter_step_norm"])
        assert -1.0 <= run["waveform_correlation"] <= 1.0
        assert 0.0 <= run["global_phase_coherence"] <= 1.0
        assert len(run["group_phase_coherence"]) == 3
        assert all(0.0 <= value <= 1.0 for value in run["group_phase_coherence"])


def test_seeded_numerical_receipt_is_deterministic(tmp_path: Path) -> None:
    args = ("--seeds", "17", "--max-steps", "600")
    first, _ = run_diagnostic(tmp_path, *args, leaf="first")
    second, _ = run_diagnostic(tmp_path, *args, leaf="second")

    assert first["target"] == second["target"]
    assert first["runs"] == second["runs"]
    assert first["comparison_by_count"] == second["comparison_by_count"]


def test_comparison_surface_does_not_encode_a_required_369_ranking(tmp_path: Path) -> None:
    payload, _out_dir = run_diagnostic(tmp_path)

    assert payload["comparison_policy"] == {
        "same_frequency_support": True,
        "ranking_required": False,
        "nine_superiority_assumed": False,
    }
    assert set(payload["comparison_by_count"]) == {"3", "6", "9"}
    assert payload["promotion"]["flags"]["three_six_nine_superiority_promoted"] is False


def test_agda_receipt_keeps_numerical_execution_and_semantic_promotion_separate() -> None:
    receipt = RECEIPT.read_text(encoding="utf-8")
    aggregate = AGGREGATE.read_text(encoding="utf-8")

    required_receipt_tokens = [
        "module DASHI.Cognition.PNF.ContinuousOscillatorSyntheticReceipt where",
        "syntheticThreeConditionExecuted",
        "syntheticSixConditionExecuted",
        "syntheticNineConditionExecuted",
        "fixedFrequencies",
        "neuroscienceInterpretationPromoted",
        "memoryMechanismPromoted",
        "hebbianIdentityPromoted",
        "kuramotoIdentityPromoted",
        "cognitiveDissonanceIdentityPromoted",
        "empiricalBrainFitPromoted",
        "threeSixNineSuperiorityPromoted",
        "quantumInterpretationPromoted",
        "syntheticThreeConditionExecutedIsTrue",
        "syntheticSixConditionExecutedIsTrue",
        "syntheticNineConditionExecutedIsTrue",
        "fixedFrequenciesIsTrue",
        "neuroscienceInterpretationPromotedIsFalse",
        "threeSixNineSuperiorityPromotedIsFalse",
    ]
    for token in required_receipt_tokens:
        assert token in receipt

    assert (
        "import DASHI.Cognition.PNF.ContinuousOscillatorSyntheticReceipt"
        in aggregate
    )
