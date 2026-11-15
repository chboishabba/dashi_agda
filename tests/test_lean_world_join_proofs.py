#!/usr/bin/env python3
"""Source-to-Lean import graph and direct original-theorem reuse tests."""
from __future__ import annotations
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_join_proofs import (
    JoinError,generate_joins,names_from_import_line,
    parse_imports,path_for_module,run_compiler)

class JoinProofPureTests(unittest.TestCase):
    def test_imports_are_original_module_references(self):
        raw=b"""module
public import Batteries.Tactic.Alias
import Batteries.Data.List.Basic Lean
-- this comment is not an import
private import Batteries.Util.Test
"""
        self.assertEqual(parse_imports(raw),(
            "Batteries.Tactic.Alias","Batteries.Data.List.Basic",
            "Lean","Batteries.Util.Test"))
        self.assertEqual(path_for_module("Batteries.Data.List.Basic"),
                         "Batteries/Data/List/Basic.lean")

    def test_comments_do_not_invent_additional_dependencies(self):
        raw=b"""/-
        import Fake.Owner
        /- import Fake.Nested -/
        -/
        module
        public import Batteries.Logic
        -- import Fake.LineComment
        namespace Example
        /- documentation
        import Fake.Late
        -/
        theorem checked : True := trivial
        """
        self.assertEqual(parse_imports(raw),("Batteries.Logic",))

    def test_unsupported_import_is_not_silently_discarded(self):
        with self.assertRaises(JoinError):
            parse_imports(b"import A.???")

    def test_safe_module_identifiers_only(self):
        for value in ("../A","Foo/Bar","A;#check","", "Foo..Bar"):
            with self.assertRaises(JoinError):
                path_for_module(value)

    def test_multiple_theorem_aliases_have_real_original_value_references(self):
        source=generate_joins("Batteries.Data.List.Basic",[
            "List.takeD_zero","List.takeD_nil","List.takeD_succ"
        ]).decode()
        self.assertEqual(source.count("Declaration.thmDecl"),4)
        self.assertEqual(source.count("let proof := mkConst donor levels"),3)
        self.assertIn("info.type",source)
        self.assertIn("info.levelParams",source)
        self.assertNotIn("sorry",source.lower())
        self.assertIn("DASHIJoined.join2",source)
        self.assertIn("DASHIJoined.combined",source)
        self.assertIn("mkConst `And.intro",source)
        self.assertIn("mkConst `And",source)

    def test_actual_combination_can_depend_on_two_original_projects(self):
        code=generate_joins((
            "Mathlib.Logic.Basic","Batteries.Data.List.Basic"),
            ["congr_heq","List.takeD_zero"]).decode()
        self.assertIn("import Mathlib.Logic.Basic",code)
        self.assertIn("import Batteries.Data.List.Basic",code)
        self.assertIn("let donors : Array Name := #[`congr_heq,`List.takeD_zero]",code)
        self.assertIn("DASHIJoined.combined",code)
        self.assertIn("And.intro",code)
    def test_duplicate_theorem_list_fails_closed(self):
        with self.assertRaises(JoinError):
            generate_joins("Batteries.Data.List.Basic",
                           ["List.takeD_zero","List.takeD_zero"])

    def test_multimodule_import_does_not_invent_proof_dependencies(self):
        source=generate_joins("Batteries.Data.List.Basic",
                              ["List.takeD_zero"]).decode()
        self.assertTrue(source.startswith("import Batteries.Data.List.Basic"))
        self.assertIn("#print axioms DASHIJoined.join0",source)


@unittest.skipUnless(os.environ.get("DASHI_LEAN_BIN"),
                     "requires explicit pinned operator Lean 4.28 executable")
class JoinProofActualLean(unittest.TestCase):
    def test_kernel_checks_two_direct_original_theorem_references(self):
        lean=Path(os.environ["DASHI_LEAN_BIN"]).resolve(strict=True)
        version=subprocess.run([str(lean),"--version"],
                               capture_output=True,check=False)
        if b"4.28.0" not in version.stdout:
            self.skipTest("not the pinned 4.28 compiler")
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            source=generate_joins("Init",["Nat.add_zero","Nat.zero_add"])
            (root/"DASHIJoinBatch.lean").write_bytes(source)
            environment={k:os.environ[k] for k in
                         ("PATH","HOME","LANG","LEAN_SYSROOT","LEAN_PATH")
                         if k in os.environ}
            digest,result=run_compiler(
                lean,root,"DASHIJoinBatch.lean",
                environment=environment,timeout=180)
            self.assertEqual(len(digest),64)
            self.assertIn(b"DASHIJoined.join0",result.stdout)
            self.assertIn(b"DASHIJoined.join1",result.stdout)
            self.assertIn(b"DASHIJoined.combined",result.stdout)


if __name__=="__main__":
    unittest.main()
