import unittest
from ksw668_f8_boundary_ray_phase import symbolic,original_t2
class BoundaryPhase(unittest.TestCase):
    def test_correct_moving_wall_pullback(self):
        self.assertTrue(symbolic()['boundary_phase_matches_bulk_original_ray'])
    def test_tangential_is_timelike_both_ends(self):
        d=original_t2();self.assertTrue(d['source_timelike_projection']);self.assertTrue(d['receiver_timelike_projection'])
    def test_inward_outward_signs_are_distinct(self):
        d=original_t2();self.assertAlmostEqual(d['source_outward_normal'],-d['source_inward_normal'])
    def test_actual_source_ray_normals(self):
        d=original_t2();self.assertGreater(d['source_inward_normal'],0);self.assertLess(d['receiver_inward_normal'],0)
    def test_no_FIO_promotion(self):
        self.assertFalse(original_t2()['FIO_transport_referee_accepted'])
if __name__=='__main__':unittest.main(verbosity=2)
