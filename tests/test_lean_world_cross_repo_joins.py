#!/usr/bin/env python3
"""Source-bound cross-repo Lean proof graph smoke on the actual PG store.

Creates tiny synthetic original source snapshots in a private test schema,
verifies cross-repository module imports and source bytes, then (only when
DASHI_LEAN_BIN is set) compiles a real theorem referring to both repositories.
Independent checking is explicitly unnecessary for this phase.
"""
from __future__ import annotations
from io import BytesIO
from pathlib import Path
import os
import sys
import tarfile
import tempfile
import unittest
import uuid

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_stream_pg import ingest_stream,migrate
from run_lean_world_join_proofs import (
    plan_multi_repo_from_pg,compile_and_join,JoinError)

try:
    import psycopg
    from psycopg import sql
except ImportError:
    psycopg=None

def archive(name,raw):
    result=BytesIO()
    with tarfile.open(fileobj=result,mode="w:gz") as tar:
        header=tarfile.TarInfo("repo/"+name)
        header.size=len(raw)
        tar.addfile(header,BytesIO(raw))
    result.seek(0)
    return result

@unittest.skipUnless(psycopg is not None and os.environ.get("PGDATABASE"),
                     "requires isolated PostgreSQL and explicit PGDATABASE")
class CrossRepoOriginalJoin(unittest.TestCase):
    def setUp(self):
        self.conn=psycopg.connect("")
        self.schema="lean_cross_join_"+uuid.uuid4().hex
        with self.conn.cursor() as cur:
            cur.execute(sql.SQL("CREATE SCHEMA {}").format(sql.Identifier(self.schema)))
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        migrate(self.conn)
        self.conn.commit()
        self.addCleanup(self.cleanup)
        self.revision1="a"*40
        self.revision2="b"*40
        self.donor=b"theorem donorAlpha : True := by trivial\n"
        self.consumer=b"import Donor\n\ntheorem consumerBeta : True := by\n  exact donorAlpha\n"
        with self.conn.transaction():
            ingest_stream(self.conn,"example/donor",self.revision1,
                          archive("Donor.lean",self.donor))
        with self.conn.transaction():
            ingest_stream(self.conn,"example/consumer",self.revision2,
                          archive("Consumer.lean",self.consumer))

    def cleanup(self):
        self.conn.rollback()
        with self.conn.cursor() as cur:
            cur.execute("RESET search_path")
            cur.execute(sql.SQL("DROP SCHEMA {} CASCADE").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        self.conn.close()

    def test_cross_repo_exact_original_import_graph(self):
        plan=plan_multi_repo_from_pg(self.conn,[
            ("example/consumer",self.revision2),
            ("example/donor",self.revision1)],["Consumer"])
        self.assertEqual(plan["order"],["Donor","Consumer"])
        self.assertEqual(plan["source"]["Donor"],self.donor)
        self.assertEqual(plan["source"]["Consumer"],self.consumer)
        self.assertEqual(plan["origins"]["Donor"]["repository"],"example/donor")
        self.assertEqual(plan["origins"]["Consumer"]["repository"],"example/consumer")

    def test_missing_snapshot_must_not_resolve_donor_from_elsewhere(self):
        with self.assertRaisesRegex(JoinError,"missing original"):
            plan_multi_repo_from_pg(self.conn,[
                ("example/consumer",self.revision2)],["Consumer"])

    def test_real_cross_repo_kernel_theorems_if_operator_pinned(self):
        executable=os.environ.get("DASHI_LEAN_BIN")
        if not executable:
            self.skipTest("set DASHI_LEAN_BIN to your Nix Lean 4.28.0")
        plan=plan_multi_repo_from_pg(self.conn,[
            ("example/consumer",self.revision2),
            ("example/donor",self.revision1)],["Consumer"])
        result=compile_and_join(plan,Path(executable),
                                ["consumerBeta","donorAlpha"])
        self.assertEqual(result["module_count"],2)
        self.assertEqual(len(result["donor_names"]),2)
        self.assertTrue(result["generated_lean_proof_references_checked"])
        self.assertFalse(result["independently_checked"])
        self.assertFalse(result["world_admitted"])

if __name__=="__main__":
    unittest.main()
