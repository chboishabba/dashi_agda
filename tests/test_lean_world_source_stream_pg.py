#!/usr/bin/env python3
"""Real PostgreSQL source-byte streaming tests; run in isolated PG environment."""
from __future__ import annotations
import hashlib
from io import BytesIO
import os
from pathlib import Path
import sys
import tarfile
import unittest
import uuid

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_stream_pg import (
    ingest_stream,migrate,retrieve_source,StreamIngestError)

try:
    import psycopg
    from psycopg import sql
except ImportError:
    psycopg=None


def fixture(files):
    output=BytesIO()
    with tarfile.open(fileobj=output,mode="w:gz") as archive:
        for name,data in files:
            info=tarfile.TarInfo("root/"+name)
            info.size=len(data)
            archive.addfile(info,BytesIO(data))
    output.seek(0)
    return output


@unittest.skipUnless(psycopg is not None and os.environ.get("PGDATABASE"),
                     "psycopg and explicit isolated PGDATABASE required")
class SourceStreamPG(unittest.TestCase):
    def setUp(self):
        self.conn=psycopg.connect("")
        self.schema="lean_src_test_"+uuid.uuid4().hex
        with self.conn.cursor() as cur:
            cur.execute(sql.SQL("CREATE SCHEMA {}").format(
                sql.Identifier(self.schema)))
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        migrate(self.conn)
        self.conn.commit()
        self.rev="a"*40
        self.repo="sample/lean-source"
        self.addCleanup(self.cleanup)

    def cleanup(self):
        self.conn.rollback()
        with self.conn.cursor() as cur:
            cur.execute("RESET search_path")
            cur.execute(sql.SQL("DROP SCHEMA {} CASCADE").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        self.conn.close()

    def count(self,name):
        with self.conn.cursor() as cur:
            cur.execute(sql.SQL("SELECT count(*) FROM {}").format(
                sql.Identifier(name)))
            return cur.fetchone()[0]

    def ingest(self,files,**caps):
        with self.conn.transaction():
            return ingest_stream(self.conn,self.repo,self.rev,
                                 fixture(files),**caps)

    def test_real_original_source_bytes_retrievable(self):
        first=b"theorem keep : True := trivial\n"
        second=b"def n : Nat := 23\n"
        result=self.ingest([("A.lean",first),("sub/B.lean",second),
                            ("README.md",b"not a Lean source")])
        self.assertEqual(result["source_occurrences"],2)
        self.assertEqual(result["rest_blob_requests"],0)
        self.assertTrue(result["source_contents_persisted"])
        self.assertFalse(result["kernel_certified"])
        self.assertEqual(self.count("lean_world_source_blob"),2)
        self.assertEqual(retrieve_source(self.conn,self.repo,self.rev,
                                         "sub/B.lean"),second)
        self.assertEqual(result["source_bytes"],len(first)+len(second))

    def test_idempotent_archive_is_safe(self):
        self.ingest([("A.lean",b"example : True := trivial")])
        self.ingest([("A.lean",b"example : True := trivial")])
        self.assertEqual(self.count("lean_world_source_occurrence"),1)
        self.assertEqual(self.count("lean_world_source_archive"),1)

    def test_source_rebinding_fails_and_rolls_back(self):
        self.ingest([("A.lean",b"example : True := trivial")])
        with self.assertRaises(StreamIngestError):
            self.ingest([("A.lean",b"example : False := by sorry")])
        self.assertEqual(self.count("lean_world_source_occurrence"),1)
        self.assertEqual(
            retrieve_source(self.conn,self.repo,self.rev,"A.lean"),
            b"example : True := trivial")

    def test_partial_new_archive_rolls_back_all_source_bytes(self):
        with self.assertRaises(StreamIngestError):
            self.ingest([("A.lean",b"ok"),("B.lean",b"large")],
                        max_source_bytes=2)
        self.assertEqual(self.count("lean_world_source_occurrence"),0)
        self.assertEqual(self.count("lean_world_source_blob"),0)
        self.assertEqual(self.count("lean_world_source_archive"),0)

    def test_occurrence_budget_is_enforced_transactionally(self):
        with self.assertRaisesRegex(StreamIngestError,"occurrence cap"):
            self.ingest([("A.lean",b"a"),("B.lean",b"b")],
                        max_occurrences=1)
        self.assertEqual(self.count("lean_world_source_occurrence"),0)

    def test_source_rows_immutable(self):
        self.ingest([("A.lean",b"ok")])
        with self.assertRaises(psycopg.Error):
            with self.conn.transaction():
                with self.conn.cursor() as cur:
                    cur.execute("UPDATE lean_world_source_blob SET content=%s",
                                (b"changed",))
        self.assertEqual(retrieve_source(self.conn,self.repo,self.rev,
                                         "A.lean"),b"ok")

    def test_archive_with_no_lean_sources_is_not_complete(self):
        with self.assertRaisesRegex(StreamIngestError,"no original Lean sources"):
            self.ingest([("README.md",b"empty")])
        self.assertEqual(self.count("lean_world_source_archive"),0)


if __name__=="__main__":
    unittest.main()
