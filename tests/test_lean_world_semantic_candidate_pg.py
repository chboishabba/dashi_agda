#!/usr/bin/env python3
"""Offline native-checker receipt binding into existing canonical candidate DAG."""
from __future__ import annotations
import base64
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_semantic_candidate_pg import (
    load_acceptance,SemanticCandidateError)

REV="a"*40
REPO="chboishabba/dashi_agda"

def write_rows(path, rows):
    raw=("".join(json.dumps(r,sort_keys=True)+"\n" for r in rows)).encode()
    path.write_bytes(raw)
    return sha256(raw).hexdigest()

class EvidenceBinding(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.sources=[]
        self.exports=[]
        self.declarations=[]
        for i,name in enumerate(("Donor.foo","Consumer.foo")):
            path=f"tests/fixtures/{i}.lean"
            content=name.encode()
            hash_=sha256(content).hexdigest()
            export_hash=sha256(b"export"+content).hexdigest()
            self.sources.append({
                "kind":"world-source-occurrence",
                "status":"source-verified-not-elaborated",
                "repository":REPO,"revision":REV,"path":path,
                "sha256":hash_
            })
            self.exports.append({
                "kind":"lean-elaborated-export",
                "repository":REPO,"revision":REV,"path":path,
                "declaration":name,"source_sha256":hash_,
                "native_export_sha256":export_hash,
                "kernel_certified":False,"world_admitted":False,
                "proof_digest":sha256(b"proof"+content).hexdigest(),
                "profile":"lean4-4.28.0-pinned",
                "type_head":"forallE","universe_shape":"[]",
                "canonical_type_b64":base64.b64encode(b"type").decode(),
                "exporter_profile":"pinned",
                "attribution":"original",
                "dependencies":[{"repository":REPO,"revision":REV,
                                 "declaration":"Donor.foo"}] if i else []
            })
            self.declarations.append({
                "declaration":name,"source_sha256":hash_,
                "native_export_sha256":export_hash
            })
        self.sources.append({
            "kind":"world-source-intake-summary",
            "repository":REPO,"revision":REV,
            "source_complete":True,"skipped_sources":0,
            "admitted_source_occurrences":2
        })
        self.spath=self.root/"sources.jsonl"
        self.epath=self.root/"exports.jsonl"
        sh=write_rows(self.spath,self.sources)
        eh=write_rows(self.epath,self.exports)
        self.receipt={
            "schema":"dashi-lean-real-independent-semantic-acceptance-v1",
            "status":"independent-checker-observed-two-module-reuse",
            "original_repository":REPO,
            "original_commit":REV,
            "independent_checker_observed":True,
            "checker_kind":"rust-nanoda",
            "checker_source_sha":"418320295890faed83a96fd97907b12a3b6728c2",
            "checker_policy":{
                "permitted_axioms":["propext","Classical.choice",
                                    "Quot.sound","Lean.trustCompiler"],
                "unsafe_permit_all_axioms":False,
                "unpermitted_axiom_hard_error":False},
            "invalid_fixture_rejected":True,
            "postgres_world_admitted":False,"fibre_retrieved":False,
            "declarations":self.declarations,
            "candidate_source_world_path":str(self.spath),
            "candidate_source_world_sha256":sh,
            "candidate_export_world_path":str(self.epath),
            "candidate_export_world_sha256":eh
        }
        self.rpath=self.root/"acceptance.json"
        self.write_receipt()

    def write_receipt(self):
        self.rpath.write_text(json.dumps(self.receipt))

    def test_canonical_candidate_is_original_bound_and_sealed(self):
        world,_=load_acceptance(self.rpath)
        self.assertEqual(world.counts()["statement_exact_nodes"],1)
        self.assertEqual(world.counts()["proof_occurrences"],2)
        self.assertTrue(world._sealed)

    def test_changed_export_bytes_are_rejected(self):
        self.epath.write_text(self.epath.read_text()+" ")
        with self.assertRaisesRegex(SemanticCandidateError,"hash mismatch"):
            load_acceptance(self.rpath)

    def test_unbound_source_hash_rejected(self):
        self.declarations[0]["source_sha256"]="f"*64
        self.write_receipt()
        with self.assertRaisesRegex(SemanticCandidateError,"unbound"):
            load_acceptance(self.rpath)

    def test_false_receipt_promotion_rejected(self):
        self.receipt["postgres_world_admitted"]=True
        self.write_receipt()
        with self.assertRaisesRegex(SemanticCandidateError,"status promotion"):
            load_acceptance(self.rpath)

    def test_unresolved_dependency_fails_closed(self):
        self.exports[1]["dependencies"][0]["declaration"]="unmatched"
        self.receipt["candidate_export_world_sha256"]=write_rows(
            self.epath,self.exports)
        self.write_receipt()
        with self.assertRaisesRegex(SemanticCandidateError,"unresolved"):
            load_acceptance(self.rpath)

if __name__=="__main__":
    unittest.main()
