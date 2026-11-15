import math
import unittest
from kozyrev_logarithmic_geometry_audit import log_geometry, matched_pitch, audit

class LogGeometryAudit(unittest.TestCase):
    def test_circle_has_no_open_channel(self):
        self.assertEqual(log_geometry(0,1.5)["radial_aperture_m"],0)
        self.assertFalse(log_geometry(0,1.5)["aperture_open"])
    def test_per_turn_ratio(self):
        self.assertAlmostEqual(log_geometry(math.log(1.05)/(2*math.pi),1.5)["growth_per_turn_fraction"],.05)
    def test_matched_endpoints(self):
        b=matched_pitch(1.5,5.288760740229291,1.5)
        self.assertAlmostEqual(log_geometry(b,1.5)["outer_m"],5.288760740229291)
    def test_handedness_independent_aperture(self):
        self.assertTrue(log_geometry(.1337,1.5)["aperture_open"])
    def test_bounded_60_candidates(self):
        a=audit()
        self.assertEqual(a["counts"]["total"],60)
        self.assertEqual(a["counts"]["open_aperture"],43)
if __name__=="__main__":unittest.main()
