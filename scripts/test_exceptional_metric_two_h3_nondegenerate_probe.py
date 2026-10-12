import unittest

from scripts.exceptional_metric_two_h3_nondegenerate_probe import verify


class TwoH3NondegenerateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_aggregate_full_rank(self):
        self.assertEqual(self.out["aggregate_gram"], ((2, 0, 0), (0, 2, 0), (0, 0, 2)))
        self.assertEqual(self.out["aggregate_rank"], 3)

    def test_distinct_radicals(self):
        self.assertNotEqual(self.out["plus_radical"], self.out["minus_radical"])

    def test_distinct_h3_patches_share_one_root_line(self):
        self.assertEqual(self.out["patch_intersection_size"], 1)
        self.assertTrue(self.out["co_registration_required"])


if __name__ == "__main__":
    unittest.main()
