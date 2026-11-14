"""Synthetic single-reflection optimiser tests. No measured physics assertions."""
import math
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import kozyrev_geometry_optimizer as optim


class GeometryOptimiserTests(unittest.TestCase):
    def test_true_golden_does_not_fit_compact_envelope(self):
        r = optim.optimise(samples=72)
        self.assertFalse(r['literal_golden_spiral_admissible_with_fixed_outer_radius'])
        self.assertAlmostEqual(r['literal_golden_spiral_outer_radius_required_m'], 13.4582039325, places=7)
        self.assertAlmostEqual(r['golden_growth_correction_exponent_for_envelope'], .2514266987284, places=8)
        self.assertNotEqual(r['reference_golden_indexed_normalised']['k'],
                            r['reference_endpoint_matched_logarithmic']['k'])

    def test_endpoints_monotonic_and_degenerate_input(self):
        for k in (-2, 0, math.log(1.55 / .75), 4):
            pts = optim.vertices(k)
            self.assertAlmostEqual(pts[0][0], .75)
            self.assertAlmostEqual(pts[-1][0], -1.55, places=10)
            self.assertAlmostEqual(pts[-1][1], 0, places=10)
        self.assertIsNone(optim.vertices(0, correction=0.7))
        with self.assertRaises(ValueError):
            optim.vertices(0, panels=2)
        with self.assertRaises(ValueError):
            optim.vertices(0, handedness=0)

    def test_simple_reflection_energy_momentum_and_receiver(self):
        wall = [(1.0, -1.0), (1.0, 1.0)]
        origin = (.25, 0.0)
        out = optim.bounce(origin, (1.0, 0.0), wall, target=(0, 0), target_radius=.1)
        self.assertIsNotNone(out)
        self.assertTrue(out['capture'])
        self.assertAlmostEqual(out['energy_residual'], 0)
        self.assertAlmostEqual(out['momentum_residual'][0], 1)
        self.assertAlmostEqual(out['momentum_residual'][1], 0)

    def test_torque_orientation_flips_when_whole_experiment_reflected(self):
        mirror_y = lambda p: (p[0], -p[1])
        vertices = optim.vertices(1.0)
        other = [mirror_y(v) for v in vertices]
        source, ray, target = (.21, .10), (math.cos(.7), math.sin(.7)), (0.0, 0.0)
        a = optim.bounce(source, ray, vertices, target)
        b = optim.bounce(mirror_y(source), mirror_y(ray), other, mirror_y(target))
        self.assertIsNotNone(a)
        self.assertIsNotNone(b)
        self.assertEqual(a['capture'], b['capture'])
        self.assertAlmostEqual(a['torque'], -b['torque'], places=12)

    def test_optimizer_is_explicit_local_synthetic_screen_only(self):
        r = optim.optimise(samples=360)
        for key in ('reference_archimedean', 'reference_endpoint_matched_logarithmic',
                    'reference_golden_indexed_normalised', 'grid_optimum'):
            self.assertGreaterEqual(r[key]['capture_worst'], 0)
            self.assertLessEqual(r[key]['capture_worst'], 1)
        self.assertGreaterEqual(r['grid_optimum']['capture_worst'],
                                r['reference_archimedean']['capture_worst'])
        self.assertTrue(r['not_real_apparatus_or_physical_wave_solution'])
        self.assertTrue(r['not_evidence_for_new_torsion'])
        self.assertTrue(r['sensitivity_to_frequency_material_emitter_receiver_open'])
        self.assertEqual(r['selected_objective'],
                         'maximise worst-case one-bounce receiver hit fraction across three fixed sources')


if __name__ == '__main__':
    unittest.main()
