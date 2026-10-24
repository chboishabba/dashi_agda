from pathlib import Path
from tempfile import TemporaryDirectory
import importlib.util
import hashlib
import json
import unittest

SRC=Path(__file__).resolve().parents[1]/"scripts"/"hardt_neural_source_bytes_gate.py"
spec=importlib.util.spec_from_file_location("hardt_neural_byte_gate",SRC)
gate=importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)

class TestNeuralIntake(unittest.TestCase):
    def setUp(self):
        self.tmp=TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.manifest={"source_dataset_identifier":"synthetic-test-data",
                       "source_author":"synthetic test only",
                       "source_revision_or_doi":"test-v1",
                       "recording_modality":"human-OPM-MEG","sampling_hz":128}
        for name in gate.FILE_KEYS:
            data=(name+'-synthetic-payload').encode()
            p=self.root/(name+'.dat')
            p.write_bytes(data)
            self.manifest[name+'_file']=p.name
            self.manifest[name+'_sha256']=hashlib.sha256(data).hexdigest()
        self.p=self.root/'receipt.json'

    def check(self):
        self.p.write_text(json.dumps(self.manifest))
        return gate.audit(self.p)

    def test_bytes_not_empirical(self):
        r=self.check()
        self.assertTrue(r['three_local_file_hashes_match'])
        self.assertFalse(r['physical_field_or_remote_influence_verified'])
        self.assertFalse(r['original_author_or_instrument_identity_authenticated'])

    def test_tamper_rejected(self):
        self.check()
        (self.root/'raw_data.dat').write_bytes(b'tampered')
        with self.assertRaisesRegex(ValueError,'byte mismatch'):
            gate.audit(self.p)

    def test_parent_traversal_rejected(self):
        self.manifest['raw_data_file']='../escape.dat'
        with self.assertRaisesRegex(ValueError,'parent-traversal'):
            self.check()

    def test_nonfinite_nyquist_rejected(self):
        for value in (float('nan'),float('inf'),float('-inf'),True,8):
            self.manifest['sampling_hz']=value
            with self.subTest(value=value),self.assertRaisesRegex(ValueError,'Nyquist'):
                self.check()

    def test_synthetic_claim_rejected(self):
        self.manifest['source_origin']='synthetic'
        with self.assertRaisesRegex(ValueError,'synthetic source'):
            self.check()

if __name__=='__main__': unittest.main()
