#!/usr/bin/env python3
"""Standalone tests: python3 -m unittest discover -s tests -p 'test_lean_world_fibre_index.py'"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_fibre_index import (
    Declaration, FibreIndex, IdentityConflict, SourceOccurrence, ingest,
)


def declaration(repo="r", rev="abc", name="Nat.add_comm", digest="proof1",
                profile="lean4", head="Eq", universe="0", typ=b"elaborated:eq"):
    return Declaration(SourceOccurrence(repo, rev, name, digest, repo + " author"),
                       profile, head, universe, typ, ("Nat.add",))


class FibreIndexTests(unittest.TestCase):
    def test_idempotent_ingest(self):
        world = FibreIndex()
        a = declaration()
        self.assertEqual(ingest(world, [a, a]), 1)
        self.assertEqual(ingest(world, [a]), 0)
        self.assertEqual(world.inventory(),
                         {"occurrences": 1, "exact_statements": 1, "fibres": 1})

    def test_distinct_proofs_retained_for_same_type(self):
        world = FibreIndex()
        a = declaration()
        b = declaration(repo="s", name="plus_sym", digest="another-proof")
        ingest(world, [a, b])
        self.assertEqual(world.occurrence_count(), 2)
        self.assertEqual(world.exact_statement_count(), 1)
        self.assertEqual(world.exact_occurrences(a), (a.source, b.source))

    def test_same_fibre_is_not_same_theorem(self):
        world = FibreIndex()
        a = declaration()
        b = declaration(repo="s", typ=b"elaborated:other")
        ingest(world, [a, b])
        self.assertEqual(world.exact_statement_count(), 2)
        self.assertEqual(world.fibre_count(), 1)

    def test_conflicting_origin_fails_closed(self):
        world = FibreIndex()
        world.admit(declaration())
        with self.assertRaises(IdentityConflict):
            world.admit(declaration(digest="changed"))

    def test_foundation_profiles_do_not_merge(self):
        world = FibreIndex()
        ingest(world, [declaration(), declaration(repo="s", profile="lean4-classical")])
        self.assertEqual(world.exact_statement_count(), 2)
        self.assertEqual(world.fibre_count(), 2)

    def test_bounded_deterministic_and_reports_truncation(self):
        world = FibreIndex()
        ingest(world, [declaration(repo="z"), declaration(repo="a"), declaration(repo="m")])
        result = world.candidates("lean4", "Eq", "0", 2)
        self.assertEqual(tuple(x.repository for x in result.matches), ("a", "m"))
        self.assertEqual((result.examined, result.remaining, result.complete),
                         (2, 1, False))
        self.assertTrue(world.candidates("lean4", "Eq", "0", 3).complete)

    def test_zero_budget_and_empty_fibre(self):
        world = FibreIndex()
        world.admit(declaration())
        self.assertEqual(world.candidates("lean4", "Eq", "0", 0).remaining, 1)
        self.assertTrue(world.candidates("other", "Eq", "0", 0).complete)
        with self.assertRaises(ValueError):
            world.candidates("lean4", "Eq", "0", -1)

    def test_pinned_revision_is_part_of_identity(self):
        world = FibreIndex()
        ingest(world, [declaration(), declaration(rev="def")])
        self.assertEqual(world.occurrence_count(), 2)
        self.assertEqual(world.exact_statement_count(), 1)

    def test_rejects_missing_source_certificate_inputs(self):
        world = FibreIndex()
        with self.assertRaises(ValueError):
            world.admit(declaration(rev=""))
        with self.assertRaises(ValueError):
            world.admit(declaration(typ=b""))


if __name__ == "__main__":
    unittest.main()
