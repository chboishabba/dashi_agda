"""Cross-integrator finite NS twin contract; no Clay or physical promotion."""
import sys, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from ns_verid_cross_integrator_contact import evaluate

class TestNSVERIDCrossIntegrator(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r = evaluate(seed=101, cutoff=1, steps=2, dt=0.001)

    def test_replay(self):
        self.assertEqual(self.r, evaluate(seed=101, cutoff=1, steps=2, dt=0.001))

    def test_finite_errors(self):
        import math
        self.assertTrue(math.isfinite(self.r['modal_l2_discrepancy']))
        for value in self.r['absolute_discrepancy'].values():
            self.assertGreaterEqual(value, 0.)
            self.assertTrue(math.isfinite(value))

    def test_authority(self):
        a=self.r['authority']
        self.assertTrue(a['finite_numerical_contact'])
        for k in ('spatial_rhs_independent','rigorous_a_posteriori_error_bound',
                  'physical_measurement','continuum_or_clay_result',
                  'automatic_semantic_promotion'):
            self.assertFalse(a[k])

    def test_invalid_settings(self):
        with self.assertRaises(ValueError):
            evaluate(cutoff=0)
        with self.assertRaises(ValueError):
            evaluate(dt=-1)

if __name__ == '__main__':
    unittest.main()
