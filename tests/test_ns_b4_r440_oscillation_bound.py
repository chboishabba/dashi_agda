import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_b4_r440_oscillation_bound import certificate,exhaustive_small,covariance

class B4OscillationTests(unittest.TestCase):
    def test_exhaustive(self):
        self.assertEqual(exhaustive_small(),729)
    def test_constant_rate_exact_cancellation(self):
        left=((Q(7),Q(3)),(Q(7),Q(-2)))
        right=((Q(7),Q(99)),)
        self.assertEqual(covariance(left,right),0)
    def test_common_shift_invariance(self):
        left=((Q(2),Q(3)),(Q(4),Q(-2)))
        right=((Q(5),Q(9)),)
        shifted_left=tuple((r+Q(100),v) for r,v in left)
        shifted_right=tuple((r+Q(100),v) for r,v in right)
        self.assertEqual(certificate(left,right),certificate(shifted_left,shifted_right))
    def test_nontrivial_negative_defect(self):
        x=certificate(((Q(2),Q(4)),),((Q(3),Q(1)),))
        self.assertEqual(x["negative_defect"],"3")
if __name__=="__main__":
    unittest.main()
