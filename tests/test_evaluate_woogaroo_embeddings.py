"""Unit tests for strict evaluation guards (synthetic input only)."""
import csv
import importlib.util
from pathlib import Path
import tempfile
import unittest

MODULE = Path(__file__).resolve().parents[1] / "scripts/evaluate_woogaroo_embeddings.py"
spec = importlib.util.spec_from_file_location("woogaroo_eval", MODULE)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def row(cell, year, fold, target="1", pred="2"):
    return dict(cell=cell, year=str(year), fold=fold, target=target,
      baseline=pred, alpha=pred, tessera=pred, fused=pred,
      source_id="synthetic", model_version="mock", acquisition_quality="mock",
      ground_truth_reference="synthetic")

class TestEvaluation(unittest.TestCase):
    def test_disjoint(self):
        sample = [row("a", 2019, "train"), row("b", 2022, "test")]
        self.assertEqual(mod.require_unique_and_disjoint(sample)["test_cells"], 1)
    def test_spatial_leak(self):
        with self.assertRaisesRegex(ValueError, "spatial leakage"):
            mod.require_unique_and_disjoint([row("a", 2019, "train"), row("a", 2022, "test")])
    def test_temporal_leak(self):
        with self.assertRaisesRegex(ValueError, "temporal leakage"):
            mod.require_unique_and_disjoint([row("a", 2019, "train"), row("b", 2019, "test")])
    def test_duplicate(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            mod.require_unique_and_disjoint([row("a", 2019, "train"), row("a", 2019, "test")])
    def test_score(self):
        self.assertEqual(mod.score([row("b", 2022, "test")], "alpha")["MAE"], 1.)
    def test_nonfinite(self):
        with self.assertRaisesRegex(ValueError, "nonfinite"):
            mod.score([row("b", 2022, "test", pred="nan")], "alpha")
    def test_csv_end_to_end(self):
        rows = [row("a", 2019, "train"), row("b", 2022, "test")]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"observations.csv"
            with path.open("w", newline="") as handle:
                writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
                writer.writeheader()
                writer.writerows(rows)
            result = mod.evaluate(path)
            self.assertEqual(result["heldout_metrics"]["baseline"]["count"], 1)

if __name__ == "__main__":
    unittest.main()
