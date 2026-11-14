import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "follow_through_source_bound_sensitivity.py"
spec = importlib.util.spec_from_file_location("follow_through", SCRIPT)
ft = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ft)

HEADER = "source_id,page,model,site,cohort,domain,instrument,specification,effect,weight,status\n"

def row(model,site,spec,effect,weight=1):
    return f"DEMONSTRATION-NOT-HISTORICAL,1,{model},{site},c1,basic,TEST,{spec},{effect},{weight},inspected-original\n"

class SensitivityTests(unittest.TestCase):
    def check(self, csvtext):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"fixture.csv"
            p.write_text(csvtext)
            return ft.analyze(ft.load(p))

    def test_same_site_compare(self):
        data=HEADER+row("DI","s1","uncorrected",4)+row("B","s1","uncorrected",2)
        out=self.check(data)
        self.assertEqual(out[0]["ranking"][0]["model"],"DI")

    def test_nonshared_site_fails_closed(self):
        data=HEADER+row("DI","s1","uncorrected",4)+row("B","s2","uncorrected",2)
        self.assertEqual(self.check(data)[0]["status"],"incomparable")

    def test_separate_adjustment_specifications(self):
        data=HEADER+row("DI","s1","uncorrected",4)+row("B","s1","uncorrected",2)
        data+=row("DI","s1","corrected",1)+row("B","s1","corrected",3)
        out=self.check(data)
        self.assertEqual(len(out),2)
        self.assertNotEqual(out[0]["ranking"][0]["model"],out[1]["ranking"][0]["model"])

    def test_missing_effect_rejected(self):
        data=HEADER+row("DI","s1","uncorrected","")+row("B","s1","uncorrected",2)
        with self.assertRaises(ValueError): self.check(data)

    def test_duplicate_rejected(self):
        data=HEADER+row("DI","s1","uncorrected",4)*2
        with self.assertRaises(ValueError): self.check(data)

    def test_model_specific_weighting_rejected(self):
        data=HEADER+row("DI","s1","uncorrected",4,2)+row("B","s1","uncorrected",2,1)
        with self.assertRaisesRegex(ValueError,"unequal model weights"):
            self.check(data)

    def test_equal_point_estimate_is_tie(self):
        data=HEADER+row("DI","s1","uncorrected",2)+row("B","s1","uncorrected",2)
        self.assertEqual(self.check(data)[0]["tied_leaders"],["B","DI"])

    def test_incomplete_coverage_rejected(self):
        data=HEADER+row("DI","s1","uncorrected",4)+row("DI","s2","uncorrected",1)+row("B","s1","uncorrected",2)
        out=self.check(data)[0]
        self.assertEqual(out["status"],"incomplete-coverage")
        self.assertEqual(out["omitted_sites"],[["s2","c1"]])

    def test_model_cell_counts_explicit(self):
        data=HEADER+row("DI","s1","uncorrected",4)+row("DI","s2","uncorrected",1)+row("B","s1","uncorrected",2)
        self.assertEqual(self.check(data)[0]["cell_counts"],{"DI":2,"B":1})

if __name__ == "__main__":
    unittest.main()
