"""Exact parity of full real 728-mode helical source and older rational R829 evaluator."""
import ast
import json
from itertools import product
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]

def run(name):
    out=subprocess.check_output([sys.executable,str(ROOT/"scripts"/name)],cwd=ROOT,text=True)
    return json.loads(out)

class RealSameSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.real=run("check_ns_real_helical_same_source.py")
        cls.rational=run("check_ns_r829_rational_345_component_certificate.py")

    def test_all_eight_physical_output_rows_match(self):
        self.assertEqual(self.real["cutoff_nonzero_modes"],728)
        real=self.real["selected_output_work"]
        rational={key:row["coherent_work"]
                  for key,row in self.rational["output_rows"].items()}
        self.assertEqual(len(real),8)
        self.assertEqual(real,rational)

    def test_exact_physical_scalars(self):
        for key,old in (("coherent_work","coherent_work"),
                        ("critical_production","critical_production"),
                        ("critical_dissipation","critical_dissipation"),
                        ("selected_signed_rate","canonical_signed_rate")):
            self.assertEqual(self.real[key],self.rational["totals"][old])
        self.assertTrue(self.real["physical_rhs_real"])
        self.assertTrue(self.real["physical_rhs_divergence_free"])
        self.assertTrue(self.real["physical_helical_norms_genuine_sqrt"])

    def test_invariant_eight_mode_support_and_norms(self):
        active={(x,y,0) for x in (-3,0,3) for y in (-4,0,4)}-{(0,0,0)}
        self.assertEqual(len(active),8)
        cutoff={(x,y,z) for x,y,z in product(range(-4,5),repeat=3)}-{(0,0,0)}
        inside={tuple(a+b for a,b in zip(p,q))
                for p,q in product(active,repeat=2)
                if tuple(a+b for a,b in zip(p,q)) in cutoff}
        self.assertEqual(inside,active)
        self.assertEqual({sum(t*t for t in k) for k in active},{9,16,25})

    def test_no_formal_authority_promotion(self):
        self.assertFalse(self.real["full_real_trajectory_formalized"])
        self.assertFalse(self.real["R823_real_source_equality_kernel_checked"])
        self.assertFalse(self.real["Clay_promotion"])

if __name__=="__main__":
    unittest.main()
