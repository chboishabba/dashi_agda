#!/usr/bin/env python3
"""Real-PG original compiled theorem artifact persistence/readback negatives."""
from __future__ import annotations
from hashlib import sha256
from io import BytesIO
from pathlib import Path
import os
import sys
import tarfile
import unittest
import uuid

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_stream_pg import ingest_stream,migrate
from lean_world_compiled_join_store import (
    persist_join,fetch_join,JoinStoreError)

try:
    import psycopg
    from psycopg import sql
except ImportError:
    psycopg=None


def archive(path,raw):
    data=BytesIO()
    with tarfile.open(fileobj=data,mode="w:gz") as handle:
        item=tarfile.TarInfo("root/"+path)
        item.size=len(raw)
        handle.addfile(item,BytesIO(raw))
    data.seek(0)
    return data


@unittest.skipUnless(psycopg is not None and os.environ.get("PGDATABASE"),
                     "requires psycopg and isolated explicit PGDATABASE")
class JoinedProofArtifactPG(unittest.TestCase):
    def setUp(self):
        self.conn=psycopg.connect("")
        self.schema="lean_join_store_"+uuid.uuid4().hex
        with self.conn.cursor() as cur:
            cur.execute(sql.SQL("CREATE SCHEMA {}").format(
                sql.Identifier(self.schema)))
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        migrate(self.conn)
        self.conn.commit()
        self.addCleanup(self.cleanup)
        self.repo="example/theorems"
        self.rev="a"*40
        self.source=b"theorem originalProof : True := by trivial\n"
        with self.conn.transaction():
            ingest_stream(self.conn,self.repo,self.rev,
                          archive("Original.lean",self.source))
        self.joined=b"import Original\n"
        self.olean=b"fake-non-certified-olean-test-bytes"
        self.report={
            "status":"original-lean-theorem-joins-compiled",
            "lean_binary_sha256":sha256(b"pinned-lean").hexdigest(),
            "lean_version":"Lean 4.28.0 test fixture",
            "generated_join_source_sha256":sha256(self.joined).hexdigest(),
            "joined_olean_sha256":sha256(self.olean).hexdigest(),
            "module_count":1,
            "root_module":"Original",
            "original_source_snapshots":[{
                "repository":self.repo,"revision":self.rev}],
            "donor_names":["originalProof"],
            "compiled_modules":[{
                "module":"Original",
                "source_sha256":sha256(self.source).hexdigest(),
                "olean_sha256":sha256(b"original-module-olean").hexdigest(),
                "direct_imports":[],
                "original_source_origin":{
                    "repository":self.repo,"revision":self.rev,
                    "path":"Original.lean",
                    "source_sha256":sha256(self.source).hexdigest()
                }
            }],
            "independently_checked":False,
            "world_admitted":False
        }

    def cleanup(self):
        self.conn.rollback()
        with self.conn.cursor() as cur:
            cur.execute("RESET search_path")
            cur.execute(sql.SQL("DROP SCHEMA {} CASCADE").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        self.conn.close()

    def test_persist_exact_original_bytes_retrieve_and_retry(self):
        first=persist_join(self.conn,self.report,self.joined,self.olean)
        second=persist_join(self.conn,self.report,self.joined,self.olean)
        self.assertEqual(first,second)
        self.assertTrue(first["content_stored_in_postgresql"])
        self.assertFalse(first["world_admitted"])
        self.assertEqual(fetch_join(self.conn,first["batch_sha256"]),
                         (self.joined,self.olean))

    def test_reject_unbound_original_module(self):
        self.report["compiled_modules"][0]["source_sha256"]="f"*64
        with self.assertRaisesRegex(JoinStoreError,"source sha mismatch"):
            persist_join(self.conn,self.report,self.joined,self.olean)

    def test_reject_forged_certificate(self):
        self.report["world_admitted"]=True
        with self.assertRaisesRegex(JoinStoreError,"cannot be promoted"):
            persist_join(self.conn,self.report,self.joined,self.olean)

    def test_reject_modified_checked_olean_payload(self):
        with self.assertRaisesRegex(JoinStoreError,"digest"):
            persist_join(self.conn,self.report,self.joined,self.olean+b"tamper")

    def test_immutable_database_join_rows(self):
        result=persist_join(self.conn,self.report,self.joined,self.olean)
        with self.assertRaises(psycopg.Error):
            with self.conn.transaction():
                with self.conn.cursor() as cur:
                    cur.execute("UPDATE lean_world_compiled_join_batch SET compiled_source=%s",
                                (b"changed",))
        self.assertEqual(fetch_join(self.conn,result["batch_sha256"]),
                         (self.joined,self.olean))

if __name__=="__main__":
    unittest.main()
