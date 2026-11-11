#!/usr/bin/env python3
"""Offline tests for source pinning, closure, Nix version gate and cleanup."""
import base64
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_ephemeral_nix_worker import (
    WorkerError, import_modules, module_path, pinned_version,
    prepare_sources, run_worker, check_version,
)

REPO = "example/theorems"
REV = "a" * 40
TARGET = b"import Local.Helper\ntheorem yes : True := helper\n"
HELPER = b"theorem helper : True := trivial\n"
PIN = b"leanprover/lean4:v4.20.0\n"


def digest(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() +
                        bytes([0]) + raw).hexdigest()


BLOBS = {digest(raw): raw for raw in (TARGET, HELPER, PIN)}


def opener(req):
    url = req.full_url
    if "/git/trees/" in url:
        rows = []
        for path, raw in [("Target.lean", TARGET), ("Local/Helper.lean", HELPER),
                          ("lean-toolchain", PIN)]:
            rows.append({"path": path, "sha": digest(raw), "size": len(raw),
                         "type": "blob", "mode": "100644"})
        return json.dumps({"truncated": False, "tree": rows}).encode()
    sha = url.rsplit("/", 1)[-1]
    if sha in BLOBS:
        raw = BLOBS[sha]
        return json.dumps({"encoding": "base64", "size": len(raw),
                           "content": base64.b64encode(raw).decode()}).encode()
    raise AssertionError("unexpected URL " + url)


class TestLeanWorker(unittest.TestCase):
    def test_import_closure_and_pinned_git_blobs(self):
        with tempfile.TemporaryDirectory() as folder:
            sources, ext = prepare_sources(REPO, REV, "Target.lean",
                                           Path(folder), opener=opener)
            self.assertEqual(len(sources), 2)
            self.assertEqual(ext, ())
            self.assertEqual((Path(folder) / "Local/Helper.lean").read_bytes(), HELPER)
            self.assertEqual((Path(folder) / "Target.lean").read_bytes(), TARGET)

    def test_public_and_protected_import_closure(self):
        from lean_ephemeral_nix_worker import local_compilation_order
        self.assertEqual(import_modules(
            b"public import Local.Helper\nprotected import Init\n"),
            ("Local.Helper", "Init"))
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "Local").mkdir()
            (root / "Target.lean").write_bytes(
                b"public import Local.Helper\ntheorem x : True := helper\n")
            (root / "Local/Helper.lean").write_bytes(HELPER)
            self.assertEqual(local_compilation_order(root, "Target.lean"),
                             ["Local/Helper.lean", "Target.lean"])

    def test_pinned_toolchain(self):
        from lean_ephemeral_nix_worker import tree_entries
        tree = tree_entries(REPO, REV, opener=opener)
        self.assertEqual(pinned_version(REPO, REV, tree, opener=opener), "4.20.0")

    def test_rejects_unsafe_module_name(self):
        with self.assertRaises(WorkerError):
            module_path("../Outside")
        with self.assertRaises(WorkerError):
            import_modules(b"import Foo / unsafe\n")

    def test_version_mismatch_fails_closed(self):
        class Result:
            returncode = 0
            stdout = "Lean (version 4.19.0, x86_64)"
        with patch("lean_ephemeral_nix_worker.subprocess.run", return_value=Result()):
            with self.assertRaises(WorkerError):
                check_version("lean", "4.20.0")

    def test_receipt_cleanup_and_no_ast_promotion(self):
        captured = []
        def checked(lean, root, target, *, timeout, memory_mib, lean_path):
            captured.append(root)
            self.assertTrue((root / target).is_file())
            return {"exit_code": 0, "olean_emitted": True,
                    "elapsed_seconds": 0.1, "stdout_tail": "", "stderr_tail": ""}
        with patch("lean_ephemeral_nix_worker.check_version",
                   return_value="Lean (version 4.20.0)"):
            result = run_worker(REPO, REV, "Target.lean", opener=opener,
                                checker=checked)
        self.assertEqual(result["status"], "lean-module-checked")
        self.assertFalse(result["declaration_ast_exported"])
        self.assertFalse(captured[0].exists())
        self.assertEqual(len(result["source_closure"]), 2)

    def test_native_export_before_ephemeral_cleanup(self):
        from lean_world_native_v3_export import inspect_v3
        captured=[]
        native_raw=(b'{"meta":{"format":{"version":"3.1.0"}}}\n'
                    b'{"ie":1,"bvar":0}\n'
                    b'{"thm":{"type":1}}\n')
        def compiled(lean, root, target, *, timeout, memory_mib, lean_path):
            compiled_path=root/"Target.olean"
            compiled_path.parent.mkdir(parents=True,exist_ok=True)
            compiled_path.write_bytes(b"fake compiled olean for test")
            captured.append(root)
            return {"exit_code":0,"olean_emitted":True,
                    "elapsed_seconds":0.1,"stdout_tail":"","stderr_tail":""}
        def exported(root,module,declaration,*,command,lean_path,timeout,memory_mib):
            self.assertTrue(root.is_dir())
            self.assertEqual(module,"Target")
            self.assertEqual(declaration,"yes")
            self.assertTrue((root/"Target.olean").exists())
            return native_raw,inspect_v3(native_raw)
        with tempfile.TemporaryDirectory() as destination:
            with patch("lean_ephemeral_nix_worker.check_version",
                       return_value="Lean (version 4.20.0)"):
                receipt=run_worker(REPO,REV,"Target.lean",opener=opener,
                    checker=compiled,exporter=exported,native_declaration="yes",
                    native_out=Path(destination))
            self.assertEqual(receipt["status"],"lean-module-checked")
            self.assertTrue(receipt["declaration_ast_exported"])
            self.assertFalse(receipt["native_export"]["world_admitted"])
            self.assertFalse(receipt["native_export"]["kernel_proof_certified"])
            self.assertTrue(Path(receipt["native_export"]["artifact_path"]).is_file())
        self.assertFalse(captured[0].exists())

    def test_native_export_requires_persistent_output(self):
        def compiled(lean, root, target, *, timeout, memory_mib, lean_path):
            return {"exit_code":0,"olean_emitted":True,
                    "elapsed_seconds":0.1,"stdout_tail":"","stderr_tail":""}
        with patch("lean_ephemeral_nix_worker.check_version",
                   return_value="Lean (version 4.20.0)"):
            receipt=run_worker(REPO,REV,"Target.lean",opener=opener,
                               checker=compiled,native_declaration="yes")
        self.assertFalse(receipt["declaration_ast_exported"])
        self.assertEqual(receipt["status"],"lean-module-checked")
        self.assertIn("persistent output",receipt["error"])

    def test_external_import_rejected_without_dependency_receipt(self):
        custom_target = b"import ThirdParty.Theorem\n"
        sha = digest(custom_target)
        def with_external(req):
            if "/git/trees/" in req.full_url:
                return json.dumps({"truncated": False, "tree": [
                    {"path": "Target.lean", "sha": sha, "size": len(custom_target),
                     "type": "blob"},
                    {"path": "lean-toolchain", "sha": digest(PIN),
                     "size": len(PIN), "type": "blob"}]}).encode()
            if req.full_url.endswith(sha):
                return json.dumps({"encoding": "base64", "size": len(custom_target),
                                   "content": base64.b64encode(custom_target).decode()}).encode()
            return opener(req)
        with patch("lean_ephemeral_nix_worker.check_version",
                   return_value="Lean (version 4.20.0)"):
            result = run_worker(REPO, REV, "Target.lean",
                                opener=with_external)
        self.assertEqual(result["status"], "incomplete")
        self.assertIn("dependency closure", result["error"])

    def test_memory_limit_and_timeout_validation(self):
        from lean_ephemeral_nix_worker import execute_lean
        with self.assertRaises(WorkerError):
            execute_lean("lean", Path("/tmp"), "X.lean", timeout=0,
                         memory_mib=4096)


if __name__ == "__main__":
    unittest.main()
