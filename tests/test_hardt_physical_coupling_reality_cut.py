"""Five independent synthetic physical-comparator/source-version checks.
These are NOT empirical tests of human brain, photobiology or psi.
"""
import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

S=Path(__file__).resolve().parents[1]/"scripts"/"hardt_physical_coupling_reality_cut.py"
spec=importlib.util.spec_from_file_location("hardt_physical_reality",S)
m=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=m
spec.loader.exec_module(m)

class TestHardtPhysicalReality(unittest.TestCase):
    def test_dipole_coherent_far_field(self):
        x=m.illustrative_physics()
        self.assertAlmostEqual(x["dipole_attenuation"],1e-6)
        self.assertAlmostEqual(x["far_coherent_B_peak_T"],1e-17)

    def test_faraday_comparator_has_explicit_scope(self):
        x=m.illustrative_physics()
        self.assertGreater(x["uniform_loop_E_peak_V_per_m"],0)
        self.assertGreater(x["comparison_ratio_NOT_an_empirical_neural_threshold"],1e16)
        self.assertIn("NOT_MEASUREMENTS",x["status"])

    def test_no_band_promotion(self):
        x=m.frequency_scope()
        self.assertTrue(x["frequency_identity_refused"])

    def test_unpinned_original_archive_fails(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/"fake.zip"
            path.write_bytes(b"not the official original Biot Savart archive")
            self.assertFalse(m.audit_original_leadfields(path)["admitted"])

    def test_v1_v2_and_subjects_distinct(self):
        self.assertNotEqual(m.DATA_V2["v1_forward"],m.DATA_V2["physical_forward"])
        self.assertEqual(m.DATA_V2["participant_count"],
                         m.DATA_V2["main_count"]+m.DATA_V2["other_count"])

if __name__=="__main__":
    unittest.main()
