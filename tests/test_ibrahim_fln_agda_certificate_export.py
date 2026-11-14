"""Check bounded Agda proof export from independently verified finite traces.

The test never claims Agda kernel acceptance by seeing generated source.
Agda itself is invoked by the repository's fail-closed check script.
"""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import ibrahim_fln_agda_certificate_export as export
import ibrahim_fln_certificates as cert
from ibrahim_fln_reference_analysis import check_manifest


class FiniteAgdaExportTests(unittest.TestCase):
    def setUp(self):
        self.fixture=ROOT/'tests/fixtures/ibrahim_paper_figure_2_4.json'
        self.manifest=ROOT/'tests/fixtures/ibrahim_paper_figure_2_4.manifest.json'
        self.graph=json.loads(self.fixture.read_text())
        self.mod='DASHI.Wikimedia.GeneratedIbrahimFigureCertificateExact'

    def test_source_manifest_is_sha_bound_and_source_attributed(self):
        receipt=check_manifest(self.manifest,self.fixture)
        self.assertEqual(receipt['verified_local_graph_sha256'],
            '734512a0773c184962079ad774771aed95c012f11a2016ab06b4902a5262d215')
        self.assertIn('Danforth',receipt['source_author'])
        self.assertIn('source-figure',receipt['parser_policy'])

    def test_export_receipt_and_all_seven_refl_witnesses(self):
        out=export.agda_text(self.graph,self.mod)
        self.assertIn('module '+self.mod+' where',out)
        self.assertIn('General.finiteFirstLinkOrbitClassifies',out)
        self.assertIn('Pigeonhole.finiteFirstLinkOrbitClassifiesAutomatically',out)
        self.assertIn('Pigeonhole.allFiniteStartsEventuallyCycle next complete',out)
        self.assertIn('General.terminalBasinsPartition checkedCensus',out)
        self.assertIn('General.terminalCensusMatchesCertificate checkedCensus',out)
        self.assertEqual(out.count('= General.orbitRepeat '),7)
        self.assertIn('orbitRepeat v0 = General.orbitRepeat 0 2 refl',out)
        self.assertIn('orbitRepeat v1 = General.orbitRepeat 0 2 refl',out)
        self.assertIn('orbitRepeat v2 = General.orbitRepeat 0 2 refl',out)
        self.assertIn('orbitRepeat v3 = General.orbitRepeat 1 2 refl',out)
        self.assertIn('orbitRepeat v4 = General.orbitRepeat 1 2 refl',out)
        self.assertIn('orbitRepeat v5 = General.orbitRepeat 2 2 refl',out)
        self.assertIn('orbitRepeat v6 = General.orbitRepeat 2 2 refl',out)
        self.assertNotIn('postulate',out)
        self.assertNotIn('{!!}',out)

    def test_cli_manifest_bound_generation(self):
        with tempfile.TemporaryDirectory() as temp:
            target=Path(temp)/'generated.agda'
            p=subprocess.run([sys.executable,str(ROOT/'scripts/ibrahim_fln_agda_certificate_export.py'),
                '--input',str(self.fixture),'--manifest',str(self.manifest),
                '--module',self.mod,'--output',str(target)],
                text=True,capture_output=True)
            self.assertEqual(p.returncode,0,p.stderr)
            self.assertEqual(target.read_text(),export.agda_text(self.graph,self.mod))

    def test_fail_closed_on_partial_or_empty_or_too_large(self):
        for graph in ({},{'a':None},{'a':'missing'},
                      {str(k):str(k) for k in range(65)}):
            with self.subTest(graph=graph),self.assertRaises(ValueError):
                export.agda_text(graph,self.mod)

    def test_bad_certificate_and_unsupported_module_name(self):
        valid=cert.certify_graph(self.graph)
        forged=copy.deepcopy(valid)
        forged['traces'][0]['cycle']=['A']
        with self.assertRaises(ValueError):
            export.agda_text(self.graph,self.mod,forged)
        with self.assertRaises(ValueError):
            export.agda_text(self.graph,'not.a.ValidModule')
        with self.assertRaises(ValueError):
            export.agda_text(self.graph,'DASHI.Wikimedia.Unsafe;postulate')

if __name__=='__main__':
    unittest.main()
