from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_synthetic.py"
OUTPUT_STEM = "continuous_oscillator_synthetic"

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


def run_diagnostic(tmp_path: Path, *extra_args: str) -> tuple[dict[str, Any], Path]:
    out_dir = tmp_path / "oscillator"
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
