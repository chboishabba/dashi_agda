import math
import unittest
from kozyrev_cross_family_screen import (trace,geometry_family,categorical_27,
                                         s3_objective_permutations)
class CrossFamily(unittest.TestCase):
    def test_27_is_experiment_labels_only(self):
        self.assertEqual(len(categorical_27()),27)
        self.assertEqual(len(set(categorical_27())),27)
    def test_s3_is_six_objective_orderings(self):
        self.assertEqual(len(s3_objective_permutations()),6)
    def test_handedness_parity(self):
        points=geometry_family("log",1.5,1.5,5.288760740229291)
        p=trace(points,(2.5,0.),(math.cos(.51*math.pi),math.sin(.51*math.pi)),target_on=False)
        reversed_points=[(x,-y) for x,y in points]
        q=trace(reversed_points,(2.5,0.),(math.cos(.51*math.pi),-math.sin(.51*math.pi)),target_on=False)
        self.assertAlmostEqual(p["wall_torque_Nm"],-q["wall_torque_Nm"],places=12)
        self.assertAlmostEqual(p["dwell_ns"],q["dwell_ns"],places=8)
        self.assertEqual(p["reflections"],q["reflections"])
    def test_power_balance(self):
        points=geometry_family("arch",1.5,1.5,5.288760740229291)
        x=trace(points,(2.5,0.),(-1.,0.),target_on=False)
        self.assertAlmostEqual(x["target_W"]+x["escape_W"]+x["wall_heat_W"]+x["unresolved_W"],9000.,places=7)
if __name__=="__main__": unittest.main()
