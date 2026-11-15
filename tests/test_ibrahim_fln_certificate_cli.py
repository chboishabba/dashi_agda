"""End-to-end manifest-bound certificate CLI with explicit negative controls."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT=Path(__file__).resolve().parents[1]/'scripts'/'ibrahim_fln_reference_analysis.py'


def data_manifest(folder:Path, name:str, graph:dict[str,str|None]):
    data=folder/f'{name}.json'
    raw=json.dumps(graph,sort_keys=True).encode()
    data.write_bytes(raw)
    fields=dict(source_author='DASHI synthetic fixture',source_title=name,
                canonical_url=f'fixture:{name}',source_role='synthetic, not historical',
                version_or_revision=f'{name}-v1',parser_policy='mapping-only',
                link_selection_policy='explicit',expected_sha256=hashlib.sha256(raw).hexdigest(),
                claim_scope='finite test only',qid_status='not-applicable',dewey_status='not-applicable')
    manifest=folder/f'{name}.manifest.json'
    manifest.write_text(json.dumps(fields))
    return data,manifest


class CertificateCLITests(unittest.TestCase):
    def run_cli(self,*args:str):
        return subprocess.run([sys.executable,str(SCRIPT),*map(str,args)],
                              capture_output=True,text=True,check=False)

    def test_create_and_verify_paper_fixture(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            data,manifest=data_manifest(folder,'published-figure',
                {'A':'B','B':'C','C':'A','D':'C','E':'C','F':'E','G':'E'})
            certificate=folder/'certificate.json'
            first=self.run_cli('--input',data,'--manifest',manifest,
                               '--certificate-output',certificate)
            self.assertEqual(first.returncode,0,first.stderr)
            self.assertTrue(certificate.exists())
            report=json.loads(first.stdout)
            self.assertEqual(report['finite_certificate']['verified_start_count'],7)
            again=self.run_cli('--input',data,'--manifest',manifest,
                               '--verify-certificate',certificate)
            self.assertEqual(again.returncode,0,again.stderr)
            self.assertEqual(json.loads(again.stdout)['finite_certificate'],report['finite_certificate'])

    def test_bounded_revision_cone_and_tampering(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            old,old_manifest=data_manifest(folder,'old',{'a':'b','b':'c','c':'c','x':'x'})
            new,new_manifest=data_manifest(folder,'new',{'a':'b','b':'x','c':'c','x':'x'})
            cert=folder/'certificate.json'
            args=('--input',old,'--manifest',old_manifest,
                  '--compare',new,'--compare-manifest',new_manifest)
            created=self.run_cli(*args,'--certificate-output',cert)
            self.assertEqual(created.returncode,0,created.stderr)
            self.assertTrue(json.loads(created.stdout)['finite_certificate']['revision_cone_verified'])
            verified=self.run_cli(*args,'--verify-certificate',cert)
            self.assertEqual(verified.returncode,0,verified.stderr)
            forged=json.loads(cert.read_text())
            forged['revision_cone']['paths_to_edit'].pop('a')
            cert.write_text(json.dumps(forged))
            rejected=self.run_cli(*args,'--verify-certificate',cert)
            self.assertNotEqual(rejected.returncode,0)

    def test_explicit_cap_is_fail_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            data,manifest=data_manifest(folder,'limit',{'a':'b','b':'a'})
            cert=folder/'certificate.json'
            out=self.run_cli('--input',data,'--manifest',manifest,
                             '--certificate-output',cert,'--certificate-node-cap','1')
            self.assertNotEqual(out.returncode,0)
            self.assertFalse(cert.exists())

if __name__=='__main__':unittest.main()
