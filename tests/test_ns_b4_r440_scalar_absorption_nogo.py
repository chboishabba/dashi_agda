import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_b4_r440_scalar_absorption_nogo import minimal_violation,scalar_obstruction

class B4AbsorptionNoGo(unittest.TestCase):
    def test_exact_counterfamily(self):
        for theta,c in ((Q(0),Q(0)),(Q(1,4),Q(1)),(Q(49,100),Q(100))):
            r=minimal_violation(theta,c)
            self.assertTrue(r["violates_unqualified_absorption"])
            self.assertEqual(r["physical_NS_realizability"],"not_asserted")
    def test_scaling(self):
        self.assertEqual(scalar_obstruction(10)["signed_defect"],"10")
    def test_invalid(self):
        with self.assertRaises(ValueError):
            minimal_violation(Q(1,2))
if __name__=="__main__":
    unittest.main()
