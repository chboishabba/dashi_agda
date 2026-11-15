#!/usr/bin/env python3
"""Three-pinned-repository pilot: one source archive request each, persisted bytes.

No Git REST walk, no independent proof checker, no Lean compilation.
Requires explicit PGDATABASE; uses a dedicated named non-public schema.
The first incomplete source archive stops further repositories; completed
repository transactions remain durable and idempotently rerunnable.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

from lean_remote_archive_stream import REPO_RE,COMMIT_RE
from run_lean_world_stream_pg import SCHEMA_RE,migrate

def validate_manifest(doc):
    entries=doc.get("repositories")
    if (doc.get("schema_version")!=1 or
        doc.get("mode")!="source-bytes-no-independent-checker" or
        not isinstance(entries,list) or len(entries)!=3 or
        {x.get("class") for x in entries}!={"small","medium","large"}):
        raise ValueError("pilot requires three pinned size classes")
    names=set()
    for item in entries:
        repo=item.get("repository")
        rev=item.get("revision")
        if (not isinstance(repo,str) or not REPO_RE.fullmatch(repo) or
            not isinstance(rev,str) or not COMMIT_RE.fullmatch(rev) or
            repo in names):
            raise ValueError("invalid or duplicate pinned original repository")
        names.add(repo)
    return entries

def run_pilot(manifest, schema, *, script=None, timeout=3600):
    entries=validate_manifest(manifest)
    if not os.environ.get("PGDATABASE"):
        raise ValueError("PGDATABASE must be selected explicitly")
    if not SCHEMA_RE.fullmatch(schema) or schema in ("public","pg_catalog"):
        raise ValueError("dedicated non-public source schema required")
    if timeout<10 or timeout>86400:
        raise ValueError("invalid per-repository timeout")
    import psycopg
    from psycopg import sql
    # Schema is an explicit dedicated source-world namespace. Never mutate
    # arbitrary caller tables or replace any existing canonical world.
    with psycopg.connect("") as conn:
        with conn.cursor() as cur:
            cur.execute(sql.SQL("CREATE SCHEMA IF NOT EXISTS {}").format(
                sql.Identifier(schema)))
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(schema)))
        conn.commit()
        migrate(conn)
        conn.commit()
    script=Path(script or Path(__file__).resolve().parent/
                "run_lean_world_stream_pg.py")
    results=[]
    for item in entries:
        command=[sys.executable,str(script),
                 item["repository"],item["revision"],"--schema",schema]
        completed=subprocess.run(command,capture_output=True,text=True,
                                 stdin=subprocess.DEVNULL,check=False,
                                 timeout=timeout)
        if completed.returncode:
            raise RuntimeError(
                "pilot incomplete at "+item["repository"]+
                ": "+completed.stderr[-1800:])
        record=json.loads(completed.stdout)
        if (record.get("status")!="source-complete-not-elaborated" or
            record.get("skipped_sources")!=0 or
            record.get("source_contents_persisted") is not True or
            record.get("rest_blob_requests")!=0 or
            record.get("kernel_certified") is not False):
            raise RuntimeError("incomplete or falsely promoted source-world receipt")
        results.append({"class":item["class"],**record})
        print(json.dumps({"event":"repository-source-ingested",**results[-1]},
                         sort_keys=True),flush=True)
    output={
        "status":"three-original-repositories-source-ingested",
        "schema":schema,"repositories":len(results),
        "source_occurrences":sum(x["source_occurrences"] for x in results),
        "source_bytes":sum(x["source_bytes"] for x in results),
        "network_archive_requests":len(results),
        "rest_blob_requests":0,
        "source_contents_persisted":True,
        "independent_checker_required":False,
        "kernel_certified":False,
        "mathematical_world_admitted":False,
        "results":results}
    print(json.dumps(output,sort_keys=True))
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest",type=Path,default=(
        Path(__file__).resolve().parent/"manifests"/
        "lean_world_source_pilot_three_20261111.json"))
    p.add_argument("--schema",default="lean_world_source_pilot")
    p.add_argument("--timeout",type=int,default=3600)
    args=p.parse_args()
    try:
        return 0 if run_pilot(
            json.loads(args.manifest.read_text()),args.schema,
            timeout=args.timeout) else 2
    except (ValueError,OSError,RuntimeError,ImportError,
            subprocess.TimeoutExpired,json.JSONDecodeError) as exc:
        print("THREE_SOURCE_PILOT_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
