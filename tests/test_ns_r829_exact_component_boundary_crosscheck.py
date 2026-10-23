import sys
import unittest
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_r829_exact_component_boundary_crosscheck import check,BOUNDARY,EXPECTED_MODES,EXPECTED_WORK
class R829BoundaryChecks(unittest.TestCase):
    def fixture(self):
        return {"schema":"ns_r829_rational_345_component_certificate_v1",
            "repository_agda_reification_complete":False,
            "output_rows":{str(k):{"coherent_work":str(w)} for k,w in zip(EXPECTED_MODES,EXPECTED_WORK)},
            "totals":{"coherent_work":"-557627/125","canonical_signed_rate":"-28273644/125"}}
    def test_selected_row_correspondence(self):
        result=check(self.fixture(),BOUNDARY.read_text())
        self.assertEqual(len(result["checked_modes"]),8)
        self.assertFalse(result["repository_native_vector_equalities_kernel_checked"])
    def test_detect_wrong_selected_row(self):
        fixture=self.fixture()
        fixture["output_rows"][str(EXPECTED_MODES[2])]["coherent_work"]="1"
        with self.assertRaises(ValueError):
            check(fixture,BOUNDARY.read_text())
    def test_refuse_authority_promotion(self):
        fixture=self.fixture()
        fixture["repository_agda_reification_complete"]=True
        with self.assertRaises(ValueError):
            check(fixture,BOUNDARY.read_text())
if __name__=="__main__":
    unittest.main()
