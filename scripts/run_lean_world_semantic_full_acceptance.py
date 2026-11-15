#!/usr/bin/env python3
"""Ephemeral PostgreSQL + independently checked source candidate + Lean reuse.

The only DB mutation is an isolated UUID-named schema, dropped even on error.
No persistent source/world table is modified. A successful result proves a
source-bound candidate can be retrieved to elaborate the same second Lean
proof; it does NOT certify hyperfabric semantics or the checker implementation.
"""
from __future__ import annotations
from hashlib import sha256
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from uuid import uuid4

from run_lean_world_semantic_candidate_pg import load_acceptance
from lean_world_postgres_candidate import persist_candidate_world
from run_lean_world_retrieved_donor_proof import compile_retrieved

MIGRATIONS=("lean_world_fibre_search_v1.sql","lean_world_candidate_dag_v1.sql")

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--acceptance-receipt",required=True,type=Path)
    p.add_argument("--donor-source",required=True,type=Path)
    p.add_argument("--consumer-source",required=True,type=Path)
    p.add_argument("--lean",required=True,type=Path)
    p.add_argument("--output-dir",required=True,type=Path)
    args=p.parse_args()
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE required; no implicit production database")
    try:
        import psycopg
        from psycopg import sql
        world,evidence=load_acceptance(args.acceptance_receipt)
        schema="lean_semantic_"+uuid4().hex
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("CREATE SCHEMA {}").format(
                    sql.Identifier(schema)))
            conn.commit()
            try:
                with conn.cursor() as cur:
                    cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                        sql.Identifier(schema)))
                    for filename in MIGRATIONS:
                        contents=(Path(__file__).resolve().parent/"sql"/filename).read_text()
                        cur.execute(contents)
                conn.commit()
                stored=persist_candidate_world(conn,world)
                if stored["kernel_certified"] is not False:
                    raise ValueError("candidate storage improperly promoted")
                receipt=compile_retrieved(
                    conn,original_receipt=args.acceptance_receipt,
                    donor_file=args.donor_source,
                    consumer_file=args.consumer_source,
                    lean_executable=args.lean)
                receipt["postgres_candidate_counts"]=stored
                receipt["postgres_isolated_schema_cleaned"]=True
            finally:
                conn.rollback()
                with conn.cursor() as cur:
                    cur.execute("RESET search_path")
                    cur.execute(sql.SQL("DROP SCHEMA IF EXISTS {} CASCADE").format(
                        sql.Identifier(schema)))
                conn.commit()
        destination=args.output_dir.resolve()
        destination.mkdir(parents=True,exist_ok=True)
        payload=(json.dumps(receipt,sort_keys=True,separators=(",",":"))+"\n").encode()
        path=destination/(sha256(payload).hexdigest()+".semantic-full-observation.json")
        if path.is_symlink():
            raise ValueError("unsafe receipt destination")
        if path.exists():
            if path.read_bytes()!=payload:
                raise ValueError("conflicting immutable receipt")
        else:
            import tempfile
            with tempfile.NamedTemporaryFile(dir=destination,delete=False) as f:
                f.write(payload);f.flush();os.fsync(f.fileno())
                pending=Path(f.name)
            try:
                os.link(pending,path)
            finally:
                pending.unlink(missing_ok=True)
        print(json.dumps({
            "status":receipt["status"],
            "receipt":str(path),
            "isolated_postgresql_schema_cleaned":True,
            "lean_consumer_accepted":True,
            "canonical_candidate_retrieved":True,
            "kernel_certified":False,
            "world_admitted":False
        },sort_keys=True))
        return 0
    except (OSError,ValueError,ImportError,subprocess.TimeoutExpired) as exc:
        p.exit(2,"SEMANTIC_FULL_ACCEPTANCE_INCOMPLETE: "+str(exc)+"\n")

if __name__=="__main__":
    raise SystemExit(main())
