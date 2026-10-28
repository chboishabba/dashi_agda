"""Pure geometric checks for event-weighted confinement proxy."""
import unittest
from kozyrev_confinement_from_events import disk_segment_length, analyse

class DiskClipTests(unittest.TestCase):
    def test_through_disk(self):
        self.assertAlmostEqual(disk_segment_length((-2,0),(2,0),1),2)
    def test_outside(self):
        self.assertEqual(disk_segment_length((2,2),(3,2),1),0)
    def test_inner(self):
        self.assertAlmostEqual(disk_segment_length((0,0),(.3,.4),1),.5)
    def test_tangent(self):
        self.assertAlmostEqual(disk_segment_length((-2,1),(2,1),1),0)
    def test_reverse(self):
        self.assertAlmostEqual(disk_segment_length((-2,.4),(2,.4),1),
                               disk_segment_length((2,.4),(-2,.4),1))
if __name__=="__main__":unittest.main()
