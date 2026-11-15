#!/usr/bin/env python3
"""Read back an actual original Lean source blob from the complete SQL world.

Source bytes are rechecked against both Git-blob SHA1 and SHA256 on read.
Writes only a caller-designated new file, never silently overwrites a path.
No source re-fetch, REST request, Lean checker or type-identity inference.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
import os
import sys
from hashlib import sha256

from run_lean_world_stream_pg import retrieve_source,SCHEMA_RE

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--schema",required=True)
    p.add_argument("--repository",required=True)
    p.add_argument("--revision",required=True)
    p.add_argument("--path",required=True)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    if not SCHEMA_RE.fullmatch(args.schema) or args.schema=="public":
        p.error("dedicated existing SQL schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE required")
    try:
        import psycopg
        from psycopg import sql
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise ValueError("source schema not found")
            conn.commit()
            raw=retrieve_source(conn,args.repository,args.revision,args.path)
        target=args.output.resolve()
        if target.exists() or target.is_symlink():
            raise ValueError("refusing existing source output file")
        with target.open("xb") as dest:
            dest.write(raw)
            dest.flush()
            os.fsync(dest.fileno())
        print(json.dumps({
            "status":"original-source-retrieved",
            "repository":args.repository,"revision":args.revision,
            "path":args.path,"output":str(target),"bytes":len(raw),
            "sha256":sha256(raw).hexdigest(),
            "source_contents_retrieved":True,
            "kernel_certified":False
        },sort_keys=True))
        return 0
    except (OSError,ValueError,ImportError) as exc:
        print("ORIGINAL_SOURCE_RETRIEVAL_INCOMPLETE: "+str(exc),
              file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
