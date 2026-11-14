"""Synthetic exact-Git tests of the Karp stacked source import superset audit."""
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1] / "scripts"))
from check_karp21_stacked_aggregate_superset import audit, Blocked, ROOTS

def git(root,*args):
    r=subprocess.run(["git","-C",str(root),*args],check=True,
                     capture_output=True,text=True)
    return r.stdout.strip()

def module(path,imports,extra=""):
    name=path[:-5].replace("/",".")
    return f"module {name} where\n\n"+ "".join(f"import {x}\n" for x in imports)+extra

class AggregateSourceSupersetTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.repo=Path(self.temp.name)
        git(self.repo,"init","-b","main")
        git(self.repo,"config","user.name","Test")
        git(self.repo,"config","user.email","test@example.invalid")
        self.A="DASHI.Test.One"
        self.B="DASHI.Test.Two"
        self._create(self.A.replace(".","/")+".agda",f"module {self.A} where\n")
        for path in ROOTS:
            self._create(path,module(path,[self.A]))
        git(self.repo,"add",".")
        git(self.repo,"commit","-m","old")
        self.old=git(self.repo,"rev-parse","HEAD")
        git(self.repo,"checkout","-b","new")
        self._create(self.B.replace(".","/")+".agda",f"module {self.B} where\n")
        for path in ROOTS:
            self._create(path,module(path,[self.A,self.B]))
        git(self.repo,"add",".")
        git(self.repo,"commit","-m","new")
        self.new=git(self.repo,"rev-parse","HEAD")

    def tearDown(self):
        self.temp.cleanup()

    def _create(self,path,content):
        p=self.repo/path
        p.parent.mkdir(parents=True,exist_ok=True)
        p.write_text(content)

    def _modify_new(self,path,content):
        self._create(path,content)
        git(self.repo,"add",path)
        git(self.repo,"commit","-m","mutation")
        return git(self.repo,"rev-parse","HEAD")

    def test_source_additive_with_exact_module_targets(self):
        result=audit(self.repo,self.old,self.new,verify_targets=True)
        self.assertEqual(len(result["roots"]),2)
        for entry in result["roots"]:
            self.assertEqual(entry["old_imports"],1)
            self.assertEqual(entry["new_imports"],2)
            self.assertTrue(entry["all_old_imports_preserved"])
            self.assertTrue(entry["verified_direct_target_presence"])
        self.assertFalse(result["all_imports_kernel_checked"])
        self.assertFalse(result["SATNotInP_proved"])

    def test_dropped_original_import_rejected(self):
        head=self._modify_new(ROOTS[0],module(ROOTS[0],[self.B]))
        with self.assertRaises(Blocked):
            audit(self.repo,self.old,head)

    def test_duplicate_import_rejected(self):
        head=self._modify_new(ROOTS[0],module(ROOTS[0],[self.A,self.B,self.B]))
        with self.assertRaises(Blocked):
            audit(self.repo,self.old,head)

    def test_unexpected_new_theorem_in_aggregate_rejected(self):
        head=self._modify_new(ROOTS[0],module(ROOTS[0],[self.A,self.B],
                                             "fake : Set\nfake = Set\n"))
        with self.assertRaises(Blocked):
            audit(self.repo,self.old,head)

    def test_missing_new_branch_import_target_rejected(self):
        self._create(ROOTS[1],module(ROOTS[1],[self.A,"DASHI.Test.Unavailable"]))
        git(self.repo,"add",ROOTS[1])
        git(self.repo,"commit","-m","broken import")
        head=git(self.repo,"rev-parse","HEAD")
        with self.assertRaises(Blocked):
            audit(self.repo,self.old,head,verify_targets=True)

    def test_non_commit_and_malformed_sha_rejected(self):
        with self.assertRaises(Blocked):
            audit(self.repo,self.old,"a"*40)
        with self.assertRaises(Blocked):
            audit(self.repo,"main",self.new)

if __name__=="__main__":
    unittest.main()
