import unittest

from scripts.exceptional_metric_h3_weyl_coregistration_probe import verify


class H3WeylCoregistrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_weyl_pullback_matches(self):
        self.assertTrue(self.out["pulled_minus_equals_plus"])

    def test_identity_vs_weyl_coregistration(self):
        self.assertEqual(self.out["identity_coregistration_rank"], 3)
        self.assertEqual(self.out["weyl_coregistration_rank"], 2)

    def test_radical_not_resolved_by_covariant_gluing(self):
        self.assertFalse(self.out["weyl_covariant_quadratic_gluing_resolves_radical"])
        self.assertTrue(self.out["additional_nontransported_structure_required"])


if __name__ == "__main__":
    unittest.main()
