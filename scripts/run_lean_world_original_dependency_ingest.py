#!/usr/bin/env python3
"""Source-first bulk ingestion of pinned original Lean dependency snapshots.

Each original repo is stored as real source bytes in PostgreSQL, not hashes
alone. Complete snapshots are reused from PostgreSQL without HTTP.
Missing sources use one capped streaming archive request per repository.
No independent checker or REST per-blob requests.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

from run_lean_world_stream_pg import SCHEMA_RE
from lean_remote_archive_stream import REPO_RE,COMMIT_RE

def admit_manifest(conn,doc,schema):
    repos=doc.get("repositories")
    if not isinstance(repos,list) or not repos or len(repos)>16:
        raise ValueError("bounded immutable dependency manifest required")
    seen=set()
    results=[]
    with conn.cursor() as cur:
        for entry in repos:
            repository=entry.get("repository")
            revision=entry.get("revision")
            if (not isinstance(repository,str) or not REPO_RE.fullmatch(repository)
                or not isinstance(revision,str) or not COMMIT_RE.fullmatch(revision)
                or (repository,revision) in seen):
                raise ValueError("invalid or repeated immutable source dependency")
            seen.add((repository,revision))
            cur.execute("""
                SELECT source_count,source_bytes FROM lean_world_source_archive
                WHERE repository=%s AND revision=%s AND status='source-complete-not-elaborated'
            """,(repository,revision))
            item=cur.fetchone()
            if item is not None:
                cur.execute("""
                    SELECT count(*),coalesce(sum(source_size),0)
                    FROM lean_world_source_occurrence
                    WHERE repository=%s AND revision=%s
                """,(repository,revision))
                count,size=cur.fetchone()
                if (count,size)!=item:
                    raise ValueError("stored complete source snapshot has inconsistent coverage")
                results.append({
                    "repository":repository,"revision":revision,
                    "source_count":count,"source_bytes":size,
                    "already_persisted":True,"archive_requests":0})
            else:
                results.append({
                    "repository":repository,"revision":revision,
                    "already_persisted":False})
    return results

def run(doc,schema,*,timeout=3600):
    if not os.environ.get("PGDATABASE"):
        raise ValueError("PGDATABASE must be explicit")
    if not SCHEMA_RE.fullmatch(schema) or schema=="public":
        raise ValueError("dedicated source schema required")
    import psycopg
    from psycopg import sql
    with psycopg.connect("") as conn:
        with conn.cursor() as cur:
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(schema)))
            cur.execute("SELECT current_schema()")
            if cur.fetchone()[0]!=schema:
                raise ValueError("source-world schema not found")
        conn.commit()
        pending=admit_manifest(conn,doc,schema)
        conn.commit()
    results=[]
    for item in pending:
        if item["already_persisted"]:
            results.append(item)
            print(json.dumps({"event":"reused-original-source-snapshot",**item},
                             sort_keys=True),flush=True)
            continue
        command=[
            sys.executable,
            str(Path(__file__).resolve().parent/"run_lean_world_stream_pg.py"),
            item["repository"],item["revision"],"--schema",schema
        ]
        completed=subprocess.run(command,capture_output=True,text=True,
                                 timeout=timeout,stdin=subprocess.DEVNULL,
                                 check=False)
        if completed.returncode:
            raise RuntimeError("missing original dependency source: "+
                               item["repository"]+" "+completed.stderr[-2400:])
        record=json.loads(completed.stdout)
        if (record.get("status")!="source-complete-not-elaborated" or
            record.get("source_contents_persisted") is not True or
            record.get("skipped_sources")!=0 or
            record.get("rest_blob_requests")!=0 or
            record.get("kernel_certified") is not False):
            raise RuntimeError("original dependency source not admitted")
        result={"repository":item["repository"],"revision":item["revision"],
                "source_count":record["source_occurrences"],
                "source_bytes":record["source_bytes"],
                "already_persisted":False,"archive_requests":1}
        results.append(result)
        print(json.dumps({"event":"ingested-original-source-snapshot",**result},
                         sort_keys=True),flush=True)
    summary={
        "status":"all-original-source-dependency-snapshots-present",
        "repositories":len(results),
        "new_archive_requests":sum(r["archive_requests"] for r in results),
        "rest_blob_requests":0,
        "source_occurrences":sum(r["source_count"] for r in results),
        "source_bytes":sum(r["source_bytes"] for r in results),
        "kernel_certified":False,
        "independent_checker_required":False,
        "mathematical_world_admitted":False,
        "results":results
    }
    print(json.dumps(summary,sort_keys=True))
    return summary

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest",required=True,type=Path)
    p.add_argument("--schema",default="lean_world_source_pilot")
    p.add_argument("--timeout",type=int,default=3600)
    args=p.parse_args()
    try:
        doc=json.loads(args.manifest.read_text(encoding="utf-8"))
        run(doc,args.schema,timeout=args.timeout)
        return 0
    except (ValueError,OSError,ImportError,RuntimeError,
            subprocess.TimeoutExpired) as exc:
        print("ORIGINAL_DEPENDENCY_INGEST_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
