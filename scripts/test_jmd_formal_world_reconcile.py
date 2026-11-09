"""Offline regressions for JMD's deterministic, proof-authority-safe world."""
import importlib.util
import json
import sqlite3
import tempfile
import unittest
from pathlib import Path

SOURCE = Path(__file__).with_name("jmd_formal_world_reconcile.py")
spec = importlib.util.spec_from_file_location("jmd_world", SOURCE)
world = importlib.util.module_from_spec(spec)
spec.loader.exec_module(world)


def fixture():
    con = sqlite3.connect(":memory:")
    con.executescript("""
      CREATE TABLE repo_symbols(
        symbol_id TEXT PRIMARY KEY, module TEXT, language TEXT);
      CREATE TABLE repo_symbol_signatures(
        symbol_id TEXT, signature TEXT, signature_sha256 TEXT);
      CREATE TABLE repo_refs(
        from_symbol TEXT, to_symbol TEXT);
      INSERT INTO repo_symbols VALUES ('DASHI.Hecke.tau','DASHI.Hecke','agda');
      INSERT INTO repo_symbol_signatures VALUES
        ('DASHI.Hecke.tau','Hecke tau coefficient A000521','aabb');
      INSERT INTO repo_refs VALUES ('DASHI.Monster.j','DASHI.Hecke.tau');
    """)
    world.init(con)
    return con


class WorldTests(unittest.TestCase):
    def setUp(self):
        self.conn=fixture()
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.conn.close)
        self.addCleanup(self.tmp.cleanup)

    def file(self, name, rows):
        p=Path(self.tmp.name)/name
        p.write_text("".join(json.dumps(r)+"\n" for r in rows),encoding="utf-8")
        return p

    def seed(self):
        self.assertEqual(world.import_agda(self.conn,revision="a"*40),1)
        src=self.conn.execute("SELECT source_key FROM jmd_world_sources").fetchone()[0]
        return src

    def test_canonical_index_reused(self):
        self.seed()
        self.assertEqual(world.report(self.conn)["sources"],1)
        self.assertEqual(self.conn.execute("SELECT count(*) FROM repo_symbols").fetchone()[0],1)

    def test_external_source_must_be_admitted_and_pinned(self):
        r={"repository_id":7,"repository":"u/r","commit":"b"*40,
           "module":"R.Main","declaration":"R.foo","type":"Nat -> Nat"}
        p=self.file("lean.jsonl",[r])
        with self.assertRaisesRegex(ValueError,"not in admitted"):
            world.import_external(self.conn,p,{8: 'u/other'})
        self.assertEqual(world.import_external(self.conn,p,{7: 'u/r'}),1)

    def test_source_keys_stable_and_distinct(self):
        self.assertEqual(world.source_key("r","a"*40,"x"),world.source_key("r","a"*40,"x"))
        self.assertNotEqual(world.source_key("r","a"*40,"x"),world.source_key("r","b"*40,"x"))

    def test_real_external_id_does_not_prove_theorem(self):
        key=self.seed()
        p=self.file("coords.jsonl",[{"source_key":key,"external_id":"A000521",
                                      "provenance":"OEIS exact identity pointer"}])
        self.assertEqual(world.import_coordinates(self.conn,p),1)
        g=self.file("goals.jsonl",[{"goal_id":"g","module":"DASHI.Hecke",
            "proposition":"A000521 modular form coefficient"}])
        world.upsert_goals(self.conn,g)
        self.assertEqual(world.candidates(self.conn),1)
        self.assertEqual(world.report(self.conn)["executed_kernel_passes"],0)
        self.assertEqual(world.report(self.conn)["unverified_candidates_promoted"],0)

    def test_invalid_external_id_rejected(self):
        key=self.seed()
        p=self.file("coords.jsonl",[{"source_key":key,"external_id":"Q0",
                                      "provenance":"bad"}])
        with self.assertRaisesRegex(ValueError,"valid exact"):
            world.import_coordinates(self.conn,p)

    def test_goal_change_reopens_candidates_not_proof_truth(self):
        self.seed()
        p=self.file("goals.jsonl",[{"goal_id":"g","module":"DASHI.Hecke",
                                     "proposition":"Hecke tau"}])
        n,changes=world.upsert_goals(self.conn,p)
        self.assertEqual((n,changes),(1,{"g"}))
        world.candidates(self.conn)
        self.assertEqual(world.upsert_goals(self.conn,p)[1],set())
        p=self.file("goals.jsonl",[{"goal_id":"g","module":"DASHI.Hecke",
                                     "proposition":"Unrelated analytical target"}])
        self.assertEqual(world.upsert_goals(self.conn,p)[1],{"g"})
        self.assertEqual(world.report(self.conn)["executed_kernel_passes"],0)

    def test_dependency_reverse_closure(self):
        self.assertEqual(world.changed_closure(self.conn,{"DASHI.Hecke.tau"}),2)
        rows=self.conn.execute("SELECT affected_symbol FROM jmd_world_affected").fetchall()
        self.assertEqual({x[0] for x in rows},{"DASHI.Hecke.tau","DASHI.Monster.j"})

    def test_fabricated_passing_receipt_cannot_be_joined_to_new_source(self):
        key=self.seed()
        p=self.file("goals.jsonl",[{"goal_id":"g","module":"DASHI.Hecke",
                                     "proposition":"Hecke tau"}])
        world.upsert_goals(self.conn,p)
        self.conn.execute("""INSERT INTO jmd_world_attempts VALUES
         ('fabrication','g',?, 'old-goal','old-source','fake', 'rev',0,
          'DASHI.Hecke','',1,'old-source','local-pinned-Lean-checker')""",(key,))
        self.assertEqual(world.report(self.conn)["executed_kernel_passes"],0)

    def test_image_search_uses_existing_agda_index(self):
        self.seed()
        p=Path(self.tmp.name)/"terms.json"
        p.write_text(json.dumps({
            "schema":"dashi-symbol-snowball-v1",
            "groups":[{"lane":"JMD-G01","search_terms":["Hecke","tau"]}]
        }))
        self.assertEqual(world.image_owner_candidates(self.conn,p),1)
        row=self.conn.execute("SELECT image_group,symbol_id,authority FROM jmd_world_image_candidates").fetchone()
        self.assertEqual(row,("JMD-G01","DASHI.Hecke.tau","candidate-only"))

    def test_native_gap_uses_existing_requirements(self):
        self.seed()
        self.conn.execute("""CREATE TABLE repo_requirements (
          symbol_id TEXT, required_symbol TEXT, requirement_class TEXT,
          requirement_kind TEXT, source TEXT)""")
        self.conn.execute("""INSERT INTO repo_requirements VALUES
          ('DASHI.Hecke.tau','Hecke tau','formal','lemma','source:agda')""")
        self.assertEqual(world.ingest_native_gaps(self.conn),1)
        self.assertEqual(world.report(self.conn)["native_gap_candidate_edges"],1)
        self.assertEqual(world.report(self.conn)["executed_kernel_passes"],0)

    def test_agda_source_delta_selectively_reopens_dependents(self):
        self.seed()
        self.conn.execute("""UPDATE repo_symbol_signatures
             SET signature=?,signature_sha256=?
             WHERE symbol_id='DASHI.Hecke.tau'""",
                          ("new Hecke type", "cccc"))
        world.import_agda(self.conn,revision="b"*40)
        changed={r[0] for r in self.conn.execute(
            "SELECT symbol_id FROM jmd_world_source_changes")}
        self.assertEqual(changed,{"DASHI.Hecke.tau"})
        self.assertEqual(world.changed_closure(self.conn,changed),2)
        self.assertEqual(world.report(self.conn)["executed_kernel_passes"],0)
        world.import_agda(self.conn,revision="b"*40)
        self.assertEqual(world.report(self.conn)["changed_source_declarations"],0)
        self.assertEqual(world.changed_closure(self.conn,set()),0)

    def test_unpinned_agda_revision_rejected(self):
        with self.assertRaisesRegex(ValueError, "full 40"):
            world.import_agda(self.conn,revision="master")

    def test_wrong_repository_name_rejected(self):
        r={"repository_id":7,"repository":"u/evil","commit":"b"*40,
           "module":"R.Main","declaration":"R.foo","type":"Nat -> Nat"}
        with self.assertRaisesRegex(ValueError,"name disagrees"):
            world.import_external(self.conn,self.file("evil.jsonl",[r]),{7:"u/original"})

    def test_duplicate_or_nonpositive_global_ids_rejected(self):
        csv=Path(self.tmp.name)/"global.csv"
        csv.write_text("github_id,full_name\n1,user/r\n1,user/r\n")
        with self.assertRaises(ValueError):
            world.read_ids(csv)
        csv.write_text("github_id,full_name\n0,user/r\n")
        with self.assertRaises(ValueError):
            world.read_ids(csv)


if __name__=="__main__":
    unittest.main()
