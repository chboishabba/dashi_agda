"""Synthetic solar and shared objective regression, not a physical device claim."""
import math
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import kozyrev_solar_bisolver as S
import kozyrev_geometry_optimizer as G

class SolarBisolverTests(unittest.TestCase):
    def test_source_power_momentum(self):
        x=S.solar()
        self.assertEqual(x['collected_W'],10000)
        self.assertEqual(x['delivered_W'],9000)
        self.assertEqual(x['local_absorption_W'],450)
        self.assertAlmostEqual(x['full_reversal_force_ceiling_N'],20000/S.C)
    def test_loss_bounds(self):
        with self.assertRaises(AssertionError):S.solar(optical_efficiency=1.5)
        with self.assertRaises(AssertionError):S.solar(absorbed_fraction=-0.1)
    def test_each_geometry_uses_shared_focusing_and_impulse(self):
        for x in S.screen():
            self.assertEqual(x['n_input'],3)
            self.assertTrue(0<=x['focus_fraction']<=1)
            self.assertTrue(math.isfinite(x['mean_wall_angular_impulse']))
            self.assertTrue(x['first_bounce_only'])
    def test_specular_normal_impulse(self):
        v=G.bounce((2.5,0),(-1.,0.),[( (1,-1),(1,1) )])
        self.assertIsNotNone(v)
        self.assertAlmostEqual(v['energy_residual'],0)
        self.assertAlmostEqual(v['momentum_residual'][0],-1)
    def test_source_angle_matters(self):
        points=G.vertices(0)
        a=S.first_bounce_scores(points,angles=[math.pi])
        b=S.first_bounce_scores(points,angles=[math.pi-.3])
        self.assertEqual(a['n_input'],1)
        self.assertEqual(b['n_input'],1)
        self.assertTrue(a['first_bounce_only'])
if __name__=='__main__':unittest.main()
