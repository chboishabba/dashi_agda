"""Regression guards for spatial-energy proxy, not field-strength proof."""
import unittest
from kozyrev_spatial_occupancy import occupancy
class OccupancyTests(unittest.TestCase):
    def test_one_straight_ray(self):
        receipt={"schema":"kozyrev-optical-events/1","scene":{"geometry":{"inner":1,"growth":0,"turns":1,"thick":0},"tracer":{"watt":100}},"rays":[{"gate":"INTERIOR_ENTRY","source":{"point":[-0.5,0],"power_w":100},"hits":[],"terminal":{"kind":"escaped","point":[0.5,0],"power_w":100}}]}
        a=occupancy(receipt,40)
        self.assertAlmostEqual(a["equivalent_energy_J"],100/299792458,places=12)
        self.assertAlmostEqual(a["entered_W"],100)
    def test_exterior_ray_rejected(self):
        receipt={"schema":"kozyrev-optical-events/1","scene":{"geometry":{"inner":1,"growth":0,"turns":1,"thick":0},"tracer":{"watt":100}},"rays":[{"gate":"OUTSIDE_FIRST_HIT","source":{"point":[-0.5,0],"power_w":100},"hits":[],"terminal":{"kind":"escaped","point":[0.5,0],"power_w":100}}]}
        a=occupancy(receipt,40)
        self.assertEqual(a["equivalent_energy_J"],0)
        self.assertEqual(a["entered_W"],0)
if __name__ == "__main__": unittest.main()
