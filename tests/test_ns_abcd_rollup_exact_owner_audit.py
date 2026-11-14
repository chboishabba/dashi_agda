import tempfile
import shutil
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_abcd_rollup_exact_owner_audit import audit,OWNERS,ROOT

class ABCDRollupAuditTests(unittest.TestCase):
    def test_actual_owner_audit(self):
        out=audit()
        self.assertFalse(out["interpretation"]["A_B_all_canonical_physical_leaves_closed"])
        self.assertFalse(out["interpretation"]["C_D_source_alignment_equals_independent_kernel_reproduction"])
    def test_fail_closed_on_false_flag_rewrite(self):
        with tempfile.TemporaryDirectory() as td:
            tmp=Path(td)
            for relative in OWNERS.values():
                target=tmp/relative
                target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(ROOT/relative,target)
            a=tmp/OWNERS["B"]
            a.write_text(a.read_text().replace("b1PhysicalProducerClosed = false","b1PhysicalProducerClosed = true"))
            with self.assertRaises(AssertionError):
                audit(tmp)

if __name__=="__main__":
    unittest.main()
