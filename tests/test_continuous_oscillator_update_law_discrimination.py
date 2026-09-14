from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_continuous_oscillator_update_law_discrimination.py"


def test_update_law_discrimination_keeps_candidate_coordinates_typed(tmp_path: Path) -> None:
    out_dir = tmp_path / "update-law"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            "--seeds",
            "7",
            "17",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["diagnostic"] == "continuous_oscillator_update_law_discrimination"
    assert payload["status"] == "synthetic_comparator_no_identity_promotion"
    assert payload["oscillator_counts"] == [3, 6, 9]
    assert payload["candidates"] == [
        "current_gradient",
        "hebbian_style_correlation",
        "oja",
        "kuramoto",
    ]
    assert payload["source_roles"]["hebb"]["exact_equation_attributed"] is False
    assert payload["source_roles"]["oja"]["doi"] == "10.1007/BF00275687"
    assert payload["source_roles"]["kuramoto"]["doi"] == "10.1007/978-3-642-69689-3"
    assert payload["comparison_policy"]["shared_coordinate_required"] is True
    assert payload["comparison_policy"]["local_vector_similarity_is_global_reduction"] is False
    assert payload["comparison_policy"]["similarity_creates_mechanism_identity"] is False

    assert len(payload["runs"]) == 6
    for run in payload["runs"]:
        comparisons = run["comparisons"]
        assert comparisons["hebbian_style_correlation"]["coordinate"] == "amplitude"
        assert comparisons["oja"]["coordinate"] == "amplitude"
        assert comparisons["kuramoto"]["coordinate"] == "phase"
        for name in ("hebbian_style_correlation", "oja", "kuramoto"):
            item = comparisons[name]
            assert -1.0 <= item["cosine_similarity"] <= 1.0
            assert item["best_scaled_residual_ratio"] >= 0.0
            assert item["exact_reduction_proved"] is False
            assert item["empirical_mechanism_identity_proved"] is False
        assert run["frequency_coordinate_compared"] is False

    receipt = out_dir / "continuous_oscillator_update_law_discrimination.json"
    assert receipt.exists()
    assert json.loads(receipt.read_text(encoding="utf-8")) == payload
