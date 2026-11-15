"""Synthetic Git regressions for the read-only Clay PR convergence planner."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Pinned local source under test; repository has no Python package wrapper.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from plan_clay_multi_pr_integrations import plan, check_manifest


def git(root, *args):
    p = subprocess.run(["git", "-C", str(root), *args],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return p.stdout.decode().strip()


class ConvergencePlannerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.root=Path(self.tmp.name)
        git(self.root,"init","-b","master")
        git(self.root,"config","user.name","DASHI test")
        git(self.root,"config","user.email","dashi-test@example.invalid")
        self._write("DASHI/Analysis/Base.agda","module DASHI.Analysis.Base where\n")
        git(self.root,"add",".")
        git(self.root,"commit","-m","base")
        self.base=git(self.root,"rev-parse","HEAD")

    def tearDown(self):
        self.tmp.cleanup()

    def _write(self,path,content):
        file=self.root/path
        file.parent.mkdir(parents=True,exist_ok=True)
        file.write_text(content)

    def _donor(self,name,common,unique):
        git(self.root,"checkout","-b",name,"master")
        self._write("DASHI/Analysis/Common.agda",common)
        self._write(f"DASHI/Analysis/{unique}.agda",f"module DASHI.Analysis.{unique} where\n")
        git(self.root,"add",".")
        git(self.root,"commit","-m",name)
        sha=git(self.root,"rev-parse","HEAD")
        git(self.root,"checkout","master")
        return sha

    def _manifest(self,rows):
        return {"repositories":{"agda":{"baseline_ref":"master"}},
                "pr_heads":[{"repository_group":"agda","pr":i+1,
                             "sha":sha,"state":"open","lane":"TEST"}
                            for i,sha in enumerate(rows)]}

    def test_identical_sources_deduplicated_without_changing_master(self):
        one=self._donor("one","same exact donor bytes\n","First")
        two=self._donor("two","same exact donor bytes\n","Second")
        out=plan(self.root,self._manifest([one,two]),"agda",check_merge_tree=True)
        self.assertEqual(out["present_pinned"],2)
        self.assertEqual(out["divergent_path_overlaps"],[])
        self.assertEqual(len(out["identical_blob_overlaps"]),1)
        self.assertEqual(out["identical_blob_overlaps"][0]["path"],"DASHI/Analysis/Common.agda")
        self.assertEqual(git(self.root,"rev-parse","HEAD"),self.base)
        self.assertFalse(out["safe_for_unattended_bulk_merge"])
        self.assertFalse(out["can_claim_kernel_acceptance"])

    def test_divergent_same_path_refuses_false_dedup(self):
        one=self._donor("one","first version\n","First")
        two=self._donor("two","second version\n","Second")
        out=plan(self.root,self._manifest([one,two]),"agda")
        self.assertEqual(len(out["divergent_path_overlaps"]),1)
        self.assertTrue(out["needs_human_integrated_source_resolution"])
        self.assertEqual(git(self.root,"rev-parse","HEAD"),self.base)

    def test_missing_head_remains_explicit(self):
        ghost="a"*40
        out=plan(self.root,self._manifest([ghost]),"agda")
        self.assertFalse(out["all_heads_fetched"])
        self.assertEqual(out["unavailable_pinned"][0]["status"],"PINNED_COMMIT_NOT_FETCHED")
        self.assertFalse(out["can_claim_clay_result"])

    def test_duplicate_pr_and_malformed_hash_rejected(self):
        x="a"*40
        invalid=self._manifest([x])
        invalid["pr_heads"].append(dict(invalid["pr_heads"][0]))
        with self.assertRaises(ValueError):
            check_manifest(invalid,"agda")
        invalid["pr_heads"].pop()
        invalid["pr_heads"][0]["sha"]="latest"
        with self.assertRaises(ValueError):
            check_manifest(invalid,"agda")


if __name__=="__main__":
    unittest.main()
