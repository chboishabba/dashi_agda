"""Rai observational archive integrity regressions: entirely synthetic bytes."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
import check_hardt_rai_observational_archive as m


class TestArchiveAdmission(unittest.TestCase):
    def setUp(self):
        temp = TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.raw = self.root/'data.bin'
        self.raw.write_bytes(b'synthetic EEG-shaped archive fixture')
        self.metadata = self.root/'api.json'
        self.meta = dict(id=28508744, doi=m.DOI, version=1,
                         files=[dict(id=123, name='data.bin', size=self.raw.stat().st_size,
                                     computed_md5=hashlib.md5(self.raw.read_bytes()).hexdigest()),
                                dict(id=124, name='other.bin', size=3,
                                     computed_md5=hashlib.md5(b'abc').hexdigest())])
        self.manifest = dict(dataset_doi=m.DOI, article_id=28508744, version=1,
                             source_owner='Laura Rai; Guido Orgs',
                             api_snapshot_file='api.json', files=[
                                 dict(file_id=123, file_name='data.bin', relative_path='data.bin',
                                      sha256=m.digest(self.raw))])
        self.path = self.root/'manifest.json'

    def run_audit(self):
        self.metadata.write_text(json.dumps(self.meta))
        self.manifest['api_snapshot_sha256'] = m.digest(self.metadata)
        self.path.write_text(json.dumps(self.manifest))
        return m.audit(self.path)

    def test_valid_partial_bytes_still_not_science(self):
        res = self.run_audit()
        self.assertEqual(res['local_files_byte_matched'],1)
        self.assertFalse(res['all_api_listed_files_locally_checked'])
        self.assertFalse(res['paper_results_reproduced'])
        self.assertFalse(res['network_origin_of_api_snapshot_authenticated'])

    def test_full_list_bytes_still_not_experiment(self):
        other=self.root/'other.bin'; other.write_bytes(b'abc')
        self.manifest['files'].append(dict(file_id=124, file_name='other.bin',
                                           relative_path='other.bin', sha256=m.digest(other)))
        res = self.run_audit()
        self.assertTrue(res['all_api_listed_files_locally_checked'])
        self.assertFalse(res['causal_remote_effect_verified'])

    def test_original_source_doi_mismatch(self):
        self.meta['doi'] = 'another-source'
        with self.assertRaisesRegex(ValueError,'metadata mismatch'): self.run_audit()

    def test_duplicated_id(self):
        self.meta['files'].append(self.meta['files'][0].copy())
        with self.assertRaisesRegex(ValueError,'duplicate'): self.run_audit()

    def test_payload_tamper(self):
        self.manifest['files'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'SHA256'): self.run_audit()

    def test_publisher_md5_mismatch(self):
        self.meta['files'][0]['computed_md5']='0'*32
        with self.assertRaisesRegex(ValueError,'Figshare checksum'): self.run_audit()

    def test_missing_original_file_id(self):
        self.manifest['files'][0]['file_id']=125
        with self.assertRaisesRegex(ValueError,'unlisted'): self.run_audit()

    def test_no_sham_required_for_observational_EEG(self):
        res = self.run_audit()
        self.assertNotIn('sham',res)
        self.assertEqual(res['local_files_byte_matched'],1)

if __name__ == '__main__': unittest.main()
