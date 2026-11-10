#!/usr/bin/env python3
"""Offline canonical statement identity, source provenance and bounded DAG tests."""
from __future__ import annotations
import base64
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_canonical_dag import CanonicalLeanWorld, Origin, WorldError

SOURCE = {"repository":"r","revision":"a"*40,"path":"A.lean",
          "sha256":"b"*64,"status":"source-verified-not-elaborated"}


def declaration(name, typ=b"Expr.Eq true true", *, deps=(), proof=None,
                type_head="Eq"):
    return {"kind":"lean-elaborated-export","repository":"r",
            "revision":"a"*40,"path":"A.lean","source_sha256":"b"*64,
            "declaration":name,"proof_digest":proof or name,
            "profile":"lean4@nix-lock","type_head":type_head,
            "universe_shape":"0","canonical_type_b64":base64.b64encode(typ).decode(),
            "exporter_profile":"lean-source-pinned-v1",
            "attribution":"original-author",
            "dependencies":[{"repository":"r","revision":"a"*40,
                             "declaration":dep} for dep in deps]}


class Tests(unittest.TestCase):
    def setUp(self):
        self.world=CanonicalLeanWorld([SOURCE])

    def test_exact_interning_keeps_independent_proofs(self):
        self.world.admit(declaration("A",proof="p1"))
        self.world.admit(declaration("B",proof="p2"))
        self.world.seal()
        self.assertEqual(self.world.counts()["statement_exact_nodes"],1)
        self.assertEqual(self.world.counts()["proof_occurrences"],2)
        self.assertNotEqual(self.world.occurrences[Origin("r","a"*40,"A")]["proof_digest"],
                            self.world.occurrences[Origin("r","a"*40,"B")]["proof_digest"])

    def test_projection_does_not_merge_different_type_bytes(self):
        self.world.admit(declaration("A"))
        self.world.admit(declaration("B",typ=b"different"))
        self.assertEqual(self.world.counts()["statement_exact_nodes"],2)

    def test_reject_raw_source_promotion(self):
        with self.assertRaises(WorldError):
            self.world.admit(SOURCE)

    def test_reject_different_source_digest(self):
        with self.assertRaises(WorldError):
            self.world.admit(dict(declaration("A"),source_sha256="wrong"))

    def test_reject_conflicting_same_declaration_identity(self):
        self.world.admit(declaration("A"))
        with self.assertRaises(WorldError):
            self.world.admit(declaration("A",typ=b"another type"))

    def test_reject_unresolved_dependency_and_cycle(self):
        self.world.admit(declaration("B",deps=("A",)))
        with self.assertRaises(WorldError):
            self.world.seal()
        other=CanonicalLeanWorld([SOURCE])
        other.admit(declaration("A",deps=("B",)))
        other.admit(declaration("B",deps=("A",)))
        with self.assertRaises(WorldError):
            other.seal()

    def test_bounded_keyset_and_stale_generation(self):
        for name in "ABCDE":
            self.world.admit(declaration(name))
        first=self.world.fibre_candidates("lean4@nix-lock","Eq","0",2)
        self.assertEqual([m["declaration"] for m in first["matches"]],["A","B"])
        self.assertEqual(first["remaining"],3)
        second=self.world.fibre_candidates("lean4@nix-lock","Eq","0",2,
                                           first["next_cursor"])
        self.assertEqual([m["declaration"] for m in second["matches"]],["C","D"])
        self.world.admit(declaration("F"))
        with self.assertRaises(WorldError):
            self.world.fibre_candidates("lean4@nix-lock","Eq","0",2,
                                        second["next_cursor"])

    def test_context_incidence_truncation_not_proof(self):
        self.world.admit(declaration("A"))
        self.world.admit(declaration("B",deps=("A",)))
        self.world.admit(declaration("C",deps=("B",)))
        self.world.seal()
        result=self.world.context_incidence(Origin("r","a"*40,"C"),max_nodes=2)
        self.assertTrue(result["truncated"])
        self.assertFalse(result["semantic_equivalence_certified"])
        full=self.world.context_incidence(Origin("r","a"*40,"C"),max_nodes=3)
        self.assertTrue(full["complete"])
        self.assertEqual(len(full["dependency_edges"]),2)


if __name__=="__main__":
    unittest.main()
