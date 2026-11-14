"""Independent exact-arithmetic checks for the synthetic Kozyrev P2 null."""
import sys
from fractions import Fraction as Q
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import kozyrev_mirror_classical_null as null


class ClassicalNullTests(unittest.TestCase):
    def test_exact_specular_energy_and_wall_momentum(self):
        for t in ((Q(1), Q(0)), (Q(1), Q(1)), (Q(-3), Q(5))):
            for d in ((Q(2), Q(7)), (Q(-5), Q(3))):
                o = null.reflected(d, t)
                self.assertEqual(null.dot(d, d), null.dot(o, o))
                self.assertEqual(null.add(o, null.reflected_wall_impulse(d, t)), d)

    def test_parity_commutes_with_reflection_and_reverses_torque(self):
        for a, b in zip(null.synthetic_profile(), null.synthetic_profile()[1:]):
            t = null.sub(b, a)
            d = (Q(3), Q(1))
            mid = null.scale(Q(1, 2), null.add(a, b))
            self.assertEqual(null.reflected(null.parity(d), null.parity(t)),
                             null.parity(null.reflected(d, t)))
            self.assertEqual(null.sample_wall_torque(null.parity(mid), null.parity(d), null.parity(t)),
                             -null.sample_wall_torque(mid, d, t))

    def test_controls_and_fail_closed_labels(self):
        r = null.report()
        self.assertEqual(r["segments"], 12)
        self.assertTrue(r["energy_conservation_all"])
        self.assertTrue(r["momentum_balance_all"])
        self.assertTrue(r["parity_torque_reversal_all"])
        self.assertFalse(r["patented_apparatus_geometry_identified"])
        self.assertFalse(r["physical_effect_established"])
        self.assertFalse(r["novel_torsion_effect_established"])
        self.assertEqual(Q(r["spiral_wall_torque_sum"]), -Q(r["mirrored_wall_torque_sum"]))
        self.assertEqual(r["source_constraints"]["unresolved_thickness_tenths_mm"], [5, 15])

    def test_separate_spiral_circle_not_assumed_same_physics(self):
        a = null.synthetic_profile(radial_step=Q(0))
        b = null.synthetic_profile(radial_step=Q(1, 5))
        self.assertNotEqual(a, b)
        self.assertNotEqual([v["point"] for v in null.ray_fixture(a)],
                            [v["point"] for v in null.ray_fixture(b)])

    def test_adversarial_degenerate_geometries_rejected(self):
        with self.assertRaises(ValueError):
            null.reflected((Q(1), Q(0)), (Q(0), Q(0)))
        with self.assertRaises(ValueError):
            null.synthetic_profile(radial_step=Q(-1))
        with self.assertRaises(ValueError):
            null.synthetic_profile(steps=1)
        with self.assertRaises(ValueError):
            null.ray_fixture(null.synthetic_profile(), (Q(0), Q(0)))


if __name__ == "__main__":
    unittest.main()
