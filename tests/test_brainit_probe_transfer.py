"""Synthetic proof-of-execution targets, never a published NSD result."""
import json
import sys
from pathlib import Path

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments/brainit"))

from probe import pool_by_cluster, permuted_partition, ridge_probe, run_probe
from transfer import calibration_curve
from inventory import digest


def test_partition_permutation_preserves_budget():
    labels = np.array([0, 0, 1, 1, 1, 2, 2])
    shuffled = permuted_partition(labels, 42)
    assert np.array_equal(np.bincount(shuffled), np.bincount(labels))
    x = np.arange(28, dtype=float).reshape(4, 7)
    pooled = pool_by_cluster(x, labels)
    assert pooled.shape == (4, 3)
    assert pooled[0, 0] == pytest.approx(0.5)
    assert pooled[0, 1] == pytest.approx(3.0)


def test_linear_probe_uses_training_only_and_detects_noisy_controls():
    rng = np.random.default_rng(13)
    labels = np.repeat(np.arange(4), 3)
    x = rng.normal(size=(100, 12))
    target = pool_by_cluster(x, labels) @ np.array(
        [[1.0, 0], [0, 1.0], [1.0, -1], [0.3, 0.2]])
    result = run_probe(x[:75], x[75:], target[:75], target[75:],
                       list(range(75)), list(range(75, 100)), labels,
                       alpha=0.01, seeds=[3, 4, 5])
    assert result["functional_or_source_partition"]["test_mse"] < 0.001
    assert len(result["cluster_size_matched_random_controls"]) == 3
    with pytest.raises(ValueError, match="leakage"):
        run_probe(x[:75], x[75:], target[:75], target[75:],
                  list(range(75)), list(range(74, 99)), labels, 1., [1])


def test_transfer_curve_checks_same_actual_stimulus_ids(tmp_path):
    def put(filename, ids, condition="paired"):
        path = tmp_path / filename
        obj = {
            "schema": "brainit-reconstruction-evaluation-v1",
            "condition": condition, "subject": 1, "seed": 44,
            "branch": "enhanced", "metric_version": "v1",
            "artifact_hashes": {"images": "shared-test-images"},
            "rows": [{"stimulus_id": i} for i in ids],
            "aggregate": {"pixcorr": {"mean": 0.4},
                          "ssim": {"mean": 0.5}},
        }
        path.write_text(json.dumps(obj))
        return path
    p15 = put("15.json", [1, 2, 3])
    p60 = put("60.json", [1, 2, 3])
    vals = [
        {"minutes": 15, "evaluation": str(p15), "checkpoint_sha256": "a" * 64},
        {"minutes": 60, "evaluation": str(p60), "checkpoint_sha256": "b" * 64},
    ]
    curve = calibration_curve(vals)
    assert [x["minutes"] for x in curve["records"]] == [15, 60]
    assert curve["records"][0]["evaluation_sha256"] == digest(p15)
    p60 = put("60.json", [3, 2, 1])
    with pytest.raises(ValueError, match="mismatched"):
        calibration_curve(vals)
