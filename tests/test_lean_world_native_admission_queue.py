"""Native v3 handoff must remain an unadmitted, source-pinned artifact."""
import hashlib, json, sys, tempfile, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_native_admission_queue import enqueue, AdmissionError

NATIVE = b'{"meta":{"format":{"version":"3.1.0"}}}\n{"thm":{"type":1}}\n'

def sample(root):
    path = root / "native.ndjson"
    path.write_bytes(NATIVE)
    h = hashlib.sha256(NATIVE).hexdigest()
    return {
        "schema":"dashi-lean-ephemeral-native-export-v1",
        "status":"native-v3-exported-unadmitted",
        "world_admitted":False, "complete_dag_checked":False,
        "kernel_proof_certified":False,
        "repository":"org/repo", "revision":"a"*40,
        "module":"Target", "declaration":"yes",
        "toolchain":"4.28.0", "dependency_closure_id":"",
        "source_closure":[{"path":"Target.lean","sha256":"b"*64}],
        "artifact_path":str(path), "artifact_sha256":h,
        "validation":{"export_sha256":h,"syntax_v3_checked":True,
                      "dag_validated":False,"kernel_proof_verified":False,
                      "ndjson_records":2,"declaration_records":1}
    }

class Tests(unittest.TestCase):
    def test_idempotent(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); r=sample(root)
            a=enqueue(r,root/"queue");b=enqueue(r,root/"queue")
            self.assertEqual(a,b)
            self.assertEqual(len(list((root/"queue").glob("*.json"))),1)
            self.assertEqual(len(list((root/"queue").glob("*.ndjson"))),1)
            self.assertFalse(a["world_admitted"])
    def test_bad_digest(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root);r["artifact_sha256"]="0"*64
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")
    def test_bad_revision(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root);r["revision"]="master"
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")
    def test_wrong_proof_promotion(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root);r["world_admitted"]=True
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")
    def test_module_missing(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root);r["module"]="Absent"
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")
    def test_corrupt_native(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root)
            raw=b'{"meta":{"format":{"version":"3.1.0"}}}\n'
            path=root/"bad.ndjson";path.write_bytes(raw)
            r["artifact_path"]=str(path)
            r["artifact_sha256"]=hashlib.sha256(raw).hexdigest()
            r["validation"]["export_sha256"]=r["artifact_sha256"]
            r["validation"]["ndjson_records"]=1
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")
    def test_distinct_provenance(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root)
            a=enqueue(r,root/"queue")
            r["revision"]="c"*40
            b=enqueue(r,root/"queue")
            self.assertNotEqual(a["handoff_key"],b["handoff_key"])
            self.assertEqual(a["artifact_path"],b["artifact_path"])
    def test_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);r=sample(root)
            alias=root/"alias";alias.symlink_to(root/"native.ndjson")
            r["artifact_path"]=str(alias)
            with self.assertRaises(AdmissionError):enqueue(r,root/"queue")

if __name__ == "__main__": unittest.main()
