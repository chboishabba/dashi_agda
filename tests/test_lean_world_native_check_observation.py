#!/usr/bin/env python3
"""Native queue to checker observation never promotes mathematical authority."""
from hashlib import sha256
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from test_lean_world_native_admission_queue import sample
from run_lean_world_native_check_observation import observe


class NativeCheckObservation(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.receipt=self.root/"export-receipt.json"
        self.receipt.write_text(json.dumps(sample(self.root)))
        self.spool=self.root/"spool"

    def checker(self, body="print('Checked 2 declarations with no errors')"):
        # Test-only config-accepting executable; never proof authority.
        program=self.root/"test-checker.py"
        program.write_text("#!"+sys.executable+"\n"+body+"\n")
        program.chmod(0o700)
        return program,sha256(program.read_bytes()).hexdigest()

    def test_success_is_only_immutable_observation(self):
        program,pin=self.checker()
        first=observe(self.receipt,self.spool,program,pin)
        again=observe(self.receipt,self.spool,program,pin)
        self.assertEqual(first,again)
        self.assertFalse(first["kernel_certified"])
        self.assertFalse(first["world_admitted"])
        data=json.loads(Path(first["checker_observation_path"]).read_text())
        self.assertFalse(data["kernel_certified"])
        self.assertEqual(data["checker_kind"],"rust-nanoda")
        self.assertEqual(data["artifact_sha256"],
                         json.loads(self.receipt.read_text())["artifact_sha256"])

    def test_checker_rejection_never_publishes_observation(self):
        program,pin=self.checker("raise SystemExit(3)")
        with self.assertRaises(ValueError):
            observe(self.receipt,self.spool,program,pin)
        self.assertEqual(list(self.spool.glob("*.checker-observation.json")),[])

    def test_tampered_binary_pin_fails_closed(self):
        program,pin=self.checker()
        with self.assertRaises(ValueError):
            observe(self.receipt,self.spool,program,"0"*64)
        self.assertEqual(list(self.spool.glob("*.checker-observation.json")),[])

if __name__=="__main__":
    unittest.main()
