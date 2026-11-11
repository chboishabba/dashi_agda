#!/usr/bin/env python3
"""Retrieve exact original joined proof bytes from PostgreSQL, not receipts."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import sys

from run_lean_world_stream_pg import SCHEMA_RE
from lean_world_compiled_join_store import fetch_join

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--schema",required=True)
    p.add_argument("--batch",required=True,help="original compiled join batch SHA256")
    p.add_argument("--output-dir",required=True,type=Path)
    args=p.parse_args()
    if not SCHEMA_RE.fullmatch(args.schema) or args.schema=="public":
        p.error("dedicated original SQL schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE is required")
    try:
        import psycopg
        from psycopg import sql
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise ValueError("original world schema does not exist")
            conn.commit()
            source,olean=fetch_join(conn,args.batch)
        directory=args.output_dir.resolve()
        if not directory.is_dir():
            raise ValueError("output directory must already exist")
        names=("DASHIJoinBatch.lean","DASHIJoinBatch.olean")
        files=[directory/name for name in names]
        if any(path.exists() or path.is_symlink() for path in files):
            raise ValueError("will not replace an existing proof artifact")
        # Publish both originals using exclusive creation only.
        for path,raw in zip(files,(source,olean)):
            with path.open("xb") as destination:
                destination.write(raw)
                destination.flush()
                os.fsync(destination.fileno())
        print(json.dumps({
            "status":"original-joined-lean-proof-bytes-retrieved",
            "batch_sha256":args.batch,
            "source_path":str(files[0]),"olean_path":str(files[1]),
            "source_sha256":sha256(source).hexdigest(),
            "olean_sha256":sha256(olean).hexdigest(),
            "independently_checked":False,
            "world_admitted":False
        },sort_keys=True))
        return 0
    except (ValueError,OSError,ImportError) as exc:
        print("JOIN_PROOF_BYTES_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
