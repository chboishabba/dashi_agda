"""Native lean4export v3 producer: syntax gate and provenance negatives."""
import json,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_native_v3_export import (
    NativeExportError,inspect_v3,export_native,store_native)

NATIVE=(b'{"meta":{"format":{"version":"3.1.0"}}}\n'
        b'{"ie":1,"bvar":0}\n'
        b'{"thm":{"type":1}}\n')

class NativeExportTests(unittest.TestCase):
    def test_valid_envelope_is_not_full_dag(self):
        result=inspect_v3(NATIVE)
        self.assertTrue(result["syntax_v3_checked"])
        self.assertFalse(result["dag_validated"])
        self.assertFalse(result["kernel_proof_verified"])

    def test_missing_metadata_fails(self):
        with self.assertRaisesRegex(NativeExportError,"metadata"):
            inspect_v3(b'{"thm":{"type":1}}\n')

    def test_no_declarations_fails(self):
        with self.assertRaisesRegex(NativeExportError,"declarations"):
            inspect_v3(NATIVE.splitlines(keepends=True)[0])

    def test_invalid_native_json_fails(self):
        with self.assertRaises(NativeExportError):
            inspect_v3(NATIVE+b'{invalid\n')

    def test_unsafe_declaration_rejected(self):
        with self.assertRaisesRegex(NativeExportError,"invalid Lean"):
            export_native(Path("/tmp"),"Target","foo\n#eval secret")

    def test_content_addressed_artifact_idempotent(self):
        with tempfile.TemporaryDirectory() as scratch:
            root=Path(scratch)
            receipt=inspect_v3(NATIVE)
            kwargs=dict(repository="u/r",revision="a"*40,module="Target",
                        declaration="foo",
                        source_closure=[{"path":"Target.lean","sha256":"b"*64}],
                        toolchain="Lean 4.33.1",dependency_closure_id="c"*64)
            first=store_native(NATIVE,receipt,root,**kwargs)
            second=store_native(NATIVE,receipt,root,**kwargs)
            self.assertEqual(first["artifact_path"],second["artifact_path"])
            self.assertFalse(first["world_admitted"])
            self.assertFalse(first["kernel_proof_certified"])

if __name__=="__main__": unittest.main()
