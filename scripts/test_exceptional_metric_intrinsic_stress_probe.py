import unittest

from scripts.exceptional_metric_intrinsic_stress_probe import verify


class IntrinsicMetricStressTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_exact_decomposition(self):
        self.assertTrue(self.out["exact_decomposition"])
        self.assertTrue(self.out["radiation_trace_zero"])

    def test_radiation_pair_intensities(self):
        self.assertEqual(str(self.out["radiation_pair_intensities"][0]), "1/27")
        self.assertEqual(str(self.out["radiation_pair_intensities"][1]), "2/27")

    def test_vacuum_coefficient(self):
        self.assertEqual(str(self.out["vacuum_coefficient"]), "1/3")


if __name__ == "__main__":
    unittest.main()
