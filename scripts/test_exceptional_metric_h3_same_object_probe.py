import unittest

from scripts.exceptional_metric_h3_same_object_probe import verify


class ExceptionalMetricH3SameObjectTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_restricted_gram(self):
        self.assertEqual(
            self.out["restricted_gram"],
            ((1, 0, 1), (0, 1, 0), (1, 0, 1)),
        )

    def test_h3_signature(self):
        self.assertEqual(self.out["projective_patch_size"], 13)
        self.assertEqual(self.out["patch_signature_null_root_other"], (1, 6, 6))
        self.assertEqual(self.out["radical_line"], (0, 1, 1, 0, 2))

    def test_a2_cubed(self):
        self.assertEqual(self.out["a2_cubed_root_line_count"], 9)


if __name__ == "__main__":
    unittest.main()
