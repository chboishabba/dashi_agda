#!/usr/bin/env python3
"""Live candidate DAG persistence tests; isolated PostgreSQL schema only."""
from __future__ import annotations
import base64
import os
from pathlib import Path
import sys
import unittest
from uuid import uuid4

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from lean_world_canonical_dag import CanonicalLeanWorld
from lean_world_postgres_candidate import (
    persist_candidate_world, CandidatePersistenceError)

SOURCE={"repository":"r","revision":"a"*40,"path":"A.lean",
        "sha256":"b"*64,"status":"source-verified-not-elaborated"}

def row(name, *, proof=None, deps=()):
    return {"kind":"lean-elaborated-export","repository":"r",
            "revision":"a"*40,"path":"A.lean","source_sha256":"b"*64,
            "declaration":name,"proof_digest":proof or name,
            "profile":"lean4@nix-lock","type_head":"Eq","universe_shape":"0",
            "canonical_type_b64":base64.b64encode(b"Expr.Eq true true").decode(),
            "exporter_profile":"lean-source-pinned-v1","attribution":"source-author",
            "dependencies":[{"repository":"r","revision":"a"*40,
                             "declaration":d} for d in deps]}

def world(*rows):
    w=CanonicalLeanWorld([SOURCE])
    for x in rows: w.admit(x)
    w.seal()
    return w

class CandidateDatabase(unittest.TestCase):
    def setUp(self):
        if not os.getenv("PGDATABASE"):
            self.skipTest("live PostgreSQL requires explicit PGDATABASE")
        try:
            import psycopg
        except ImportError:
            self.skipTest("psycopg3 not installed")
        self.conn=psycopg.connect("")
        self.schema="candidate_test_"+uuid4().hex
        with self.conn.cursor() as cur:
            cur.execute('CREATE SCHEMA "'+self.schema+'"')
        self.conn.commit()
        with self.conn.cursor() as cur:
            cur.execute('SET search_path TO "'+self.schema+'",public')
            for file in ("lean_world_fibre_search_v1.sql",
                         "lean_world_candidate_dag_v1.sql"):
                cur.execute((ROOT/"scripts/sql"/file).read_text())
        self.conn.commit()
        self.addCleanup(self.cleanup_database)

    def cleanup_database(self):
        try:
            self.conn.rollback()
            with self.conn.cursor() as cur:
                cur.execute('RESET search_path')
                cur.execute('DROP SCHEMA IF EXISTS "'+self.schema+'" CASCADE')
            self.conn.commit()
        finally:
            self.conn.close()

    def scalar(self, sql):
        with self.conn.cursor() as cur:
            cur.execute(sql)
            return cur.fetchone()[0]

    def test_atomic_idempotent_shared_statement_and_edges(self):
        w=world(row("A"),row("B",deps=("A",)))
        a=persist_candidate_world(self.conn,w)
        b=persist_candidate_world(self.conn,w)
        self.assertEqual(a,b)
        self.assertFalse(a["kernel_certified"])
        self.assertEqual(self.scalar("SELECT count(*) FROM lean_world_statement"),1)
        self.assertEqual(self.scalar("SELECT count(*) FROM lean_world_occurrence"),2)
        self.assertEqual(self.scalar(
            "SELECT count(*) FROM lean_world_candidate_dependency"),1)
        self.assertEqual(self.scalar(
            "SELECT occurrence_count FROM lean_world_fibre"),2)

    def test_conflict_rolls_back_whole_world(self):
        persist_candidate_world(self.conn,world(row("A")))
        conflicting=world(row("A",proof="different"),row("B",deps=("A",)))
        with self.assertRaises(CandidatePersistenceError):
            persist_candidate_world(self.conn,conflicting)
        self.assertEqual(self.scalar("SELECT count(*) FROM lean_world_occurrence"),1)
        self.assertEqual(self.scalar(
            "SELECT count(*) FROM lean_world_candidate_dependency"),0)

    def test_missing_source_cannot_store(self):
        w=world(row("A"))
        w.sources.clear()
        with self.assertRaises(CandidatePersistenceError):
            persist_candidate_world(self.conn,w)
        self.assertEqual(self.scalar("SELECT count(*) FROM lean_world_occurrence"),0)

    def test_rebind_dependency_history_rejected(self):
        persist_candidate_world(self.conn,world(row("A"),row("B")))
        changed=world(row("A"),row("B",deps=("A",)))
        with self.assertRaises(CandidatePersistenceError):
            persist_candidate_world(self.conn,changed)
        self.assertEqual(self.scalar(
            "SELECT count(*) FROM lean_world_candidate_dependency"),0)

if __name__=="__main__":
    unittest.main()
