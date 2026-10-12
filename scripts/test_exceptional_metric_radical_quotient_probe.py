import unittest

from scripts.exceptional_metric_radical_quotient_probe import verify


class ExceptionalMetricRadicalQuotientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_radical_and_quotient(self):
        self.assertEqual(self.out["radical_size"], 3)
        self.assertEqual(self.out["quotient_coset_count"], 9)
        self.assertEqual(self.out["quotient_q_classes"], (1, 4, 4))

    def test_complete_multipartite_graph(self):
        self.assertEqual(
            self.out["intrinsic_graph"],
            "complete 9-partite graph with part size 3",
        )

    def test_quotient_laplacian(self):
        self.assertEqual(
            self.out["fiber_constant_laplacian"],
            "L = 27 I on mean-zero quotient functions",
        )


if __name__ == "__main__":
    unittest.main()
