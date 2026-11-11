#!/usr/bin/env python3
"""One-stream, real-byte Lean source ingestion into PostgreSQL.

No REST blobs. No repository checkout. No independent checker.
One source file at a time (8 MiB maximum) and no Python repository-sized
receipt dictionary. One SQL transaction per pinned repository: incomplete
archives leave no committed occurrences. Immutable source and archive rows
are verified byte-for-byte on idempotent retries.
"""
from __future__ import annotations
from hashlib import sha1,sha256
from pathlib import Path
import argparse
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request

from lean_remote_archive_stream import stream_archive, REPO_RE, COMMIT_RE
from lean_world_source_world import SourceWorldBuilder

class StreamIngestError(ValueError):
    pass

SCHEMA_RE=re.compile(r"[A-Za-z_][A-Za-z0-9_]{0,62}\Z")
MAX_SOURCE_BYTES=8*1024*1024
TOTAL_CAP=4*1024*1024*1024
TRANSFER_CAP=2*1024*1024*1024
MAX_OCCURRENCES=1_000_000

def migrate(conn):
    sql_text=(Path(__file__).resolve().parent/"sql"/
              "lean_world_source_stream_v1.sql").read_text()
    with conn.cursor() as cur:
        cur.execute(sql_text)

def ingest_stream(conn, repo, revision, fileobj, *,
                  max_source_bytes=MAX_SOURCE_BYTES,
                  max_total_bytes=TOTAL_CAP,
                  max_transfer_bytes=TRANSFER_CAP,
                  max_occurrences=MAX_OCCURRENCES):
    """Persist real bytes in the caller's active transaction.

    Requires a caller-managed transaction and an already selected SQL schema.
    Incomplete input must raise so the caller rolls the transaction back.
    """
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(revision):
        raise StreamIngestError("immutable source origin required")
    revision=revision.lower()
    if not 1<=max_source_bytes<=MAX_SOURCE_BYTES:
        raise StreamIngestError("per-file budget must not exceed reviewed 8 MiB")
    if max_total_bytes<=0 or max_transfer_bytes<=0:
        raise StreamIngestError("invalid aggregate cap")
    if not 1<=max_occurrences<=MAX_OCCURRENCES:
        raise StreamIngestError("invalid occurrence cap")
    count=total=skips=0
    with conn.cursor() as cur:
        def accept(receipt,raw):
            nonlocal count,total
            if count >= max_occurrences:
                raise StreamIngestError("source occurrence cap reached")
            SourceWorldBuilder._validate_receipt(receipt,raw)
            if len(raw)>max_source_bytes:
                raise StreamIngestError("unbounded original source")
            digest=bytes.fromhex(receipt["sha256"])
            git=bytes.fromhex(receipt["git_blob"])
            cur.execute("""
                INSERT INTO lean_world_source_blob
                    (sha256,git_blob_sha1,source_size,content)
                VALUES (%s,%s,%s,%s) ON CONFLICT DO NOTHING
            """,(digest,git,len(raw),raw))
            cur.execute("""
                SELECT git_blob_sha1,source_size,content
                FROM lean_world_source_blob WHERE sha256=%s
            """,(digest,))
            persisted=cur.fetchone()
            if (persisted is None or bytes(persisted[0])!=git or
                persisted[1]!=len(raw) or bytes(persisted[2])!=raw):
                raise StreamIngestError("stored original byte collision")
            cur.execute("""
                INSERT INTO lean_world_source_occurrence
                    (repository,revision,path,sha256,source_size)
                VALUES (%s,%s,%s,%s,%s) ON CONFLICT DO NOTHING
            """,(repo,revision,receipt["path"],digest,len(raw)))
            cur.execute("""
                SELECT sha256,source_size FROM lean_world_source_occurrence
                WHERE repository=%s AND revision=%s AND path=%s
            """,(repo,revision,receipt["path"]))
            old=cur.fetchone()
            if old is None or bytes(old[0])!=digest or old[1]!=len(raw):
                raise StreamIngestError("original source rebind rejected")
            count+=1
            total+=len(raw)
        for receipt in stream_archive(
            fileobj,repo,revision,max_file_bytes=max_source_bytes,
            max_total_bytes=max_total_bytes,
            max_transfer_bytes=max_transfer_bytes,
            on_source=accept
        ):
            if receipt["status"]=="skipped-size-cap":
                skips+=1
        # If skipped rows exist, the complete source claim is false.
        if skips:
            raise StreamIngestError(
                "incomplete archive: "+str(skips)+" source files exceed cap")
        if count == 0:
            raise StreamIngestError("no original Lean sources in selected archive")
        cur.execute("""
            SELECT count(*),coalesce(sum(source_size),0)
            FROM lean_world_source_occurrence
            WHERE repository=%s AND revision=%s
        """,(repo,revision))
        rows,bytes_=cur.fetchone()
        if rows!=count or bytes_!=total:
            raise StreamIngestError("source coverage differs from original archive")
        cur.execute("""
            INSERT INTO lean_world_source_archive
                (repository,revision,source_count,source_bytes,skipped_count,status)
            VALUES (%s,%s,%s,%s,0,'source-complete-not-elaborated')
            ON CONFLICT DO NOTHING
        """,(repo,revision,count,total))
        cur.execute("""
            SELECT source_count,source_bytes,skipped_count,status
            FROM lean_world_source_archive
            WHERE repository=%s AND revision=%s
        """,(repo,revision))
        if cur.fetchone()!=(count,total,0,"source-complete-not-elaborated"):
            raise StreamIngestError("archive completeness history collision")
    return {
        "status":"source-complete-not-elaborated",
        "repository":repo,"revision":revision,
        "source_occurrences":count,"source_bytes":total,
        "skipped_sources":0,"archive_requests":1,
        "rest_blob_requests":0,
        "source_contents_persisted":True,
        "lean_elaborated":False,"kernel_certified":False,"world_admitted":False
    }

def retrieve_source(conn, repo, revision, path):
    """Return exact original bytes, with fresh SHA-1 and SHA-256 verification."""
    with conn.cursor() as cur:
        cur.execute("""
            SELECT b.content,b.git_blob_sha1,b.sha256,o.source_size
            FROM lean_world_source_occurrence o
            JOIN lean_world_source_blob b ON b.sha256=o.sha256
            JOIN lean_world_source_archive a
              ON (a.repository=o.repository AND a.revision=o.revision)
            WHERE o.repository=%s AND o.revision=%s AND o.path=%s
              AND a.status='source-complete-not-elaborated'
        """,(repo,revision,path))
        row=cur.fetchone()
    if row is None:
        raise StreamIngestError("original complete source occurrence unavailable")
    raw=bytes(row[0])
    git=sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).digest()
    if (len(raw)!=row[3] or git!=bytes(row[1]) or
        sha256(raw).digest()!=bytes(row[2])):
        raise StreamIngestError("retrieved original source integrity failed")
    return raw

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("repository")
    p.add_argument("revision")
    p.add_argument("--schema",required=True)
    p.add_argument("--max-source-bytes",type=int,default=MAX_SOURCE_BYTES)
    p.add_argument("--max-total-bytes",type=int,default=TOTAL_CAP)
    p.add_argument("--max-transfer-bytes",type=int,default=TRANSFER_CAP)
    p.add_argument("--max-occurrences",type=int,default=MAX_OCCURRENCES)
    args=p.parse_args()
    if not SCHEMA_RE.fullmatch(args.schema):
        p.error("explicit safe PostgreSQL schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE required")
    try:
        import psycopg
        from psycopg import sql
        if not REPO_RE.fullmatch(args.repository) or not COMMIT_RE.fullmatch(args.revision):
            raise StreamIngestError("pinned OWNER/REPO and SHA required")
        owner,name=args.repository.split("/")
        url=("https://codeload.github.com/"+
             urllib.parse.quote(owner,safe="")+"/"+
             urllib.parse.quote(name,safe="")+"/tar.gz/"+
             args.revision.lower())
        request=urllib.request.Request(
            url,headers={"User-Agent":"dashi-source-pg-stream/1"})
        started=time.monotonic()
        with psycopg.connect("") as conn:
            with conn.transaction():
                with conn.cursor() as cur:
                    cur.execute(sql.SQL("SET LOCAL search_path TO {},pg_catalog").format(
                        sql.Identifier(args.schema)))
                    cur.execute("SELECT current_schema()")
                    if cur.fetchone()[0]!=args.schema:
                        raise StreamIngestError("target schema unavailable")
                migrate(conn)
                # Exactly one HTTPS archive retrieval per repository, only
                # after SQL schema has been selected and transaction opened.
                with urllib.request.urlopen(request,timeout=60) as archive:
                    receipt=ingest_stream(
                        conn,args.repository,args.revision,archive,
                        max_source_bytes=args.max_source_bytes,
                        max_total_bytes=args.max_total_bytes,
                        max_transfer_bytes=args.max_transfer_bytes,
                        max_occurrences=args.max_occurrences)
        receipt["elapsed_seconds"]=round(time.monotonic()-started,3)
        print(json.dumps(receipt,sort_keys=True))
        return 0
    except (Exception,) as exc:
        print("LEAN_SOURCE_PG_STREAM_INCOMPLETE: "+
              type(exc).__name__+": "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
