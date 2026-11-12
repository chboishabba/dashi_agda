#!/usr/bin/env python3
"""Real original typed Expr -> bounded fibre search + compression baseline.

Both operations consume the SAME exact type/proof DAG and original source
from the already-owned PostgreSQL world. No permanent execution traces, no
global theorem pairs, no second canonical store and no certification.
This is deliberately a baseline, not the FRACDASH generator or full MDL
acceptance: a program may replace bytes only after exact reconstruction
and total-cost/attribution checks on the exact same source objects.
"""
from __future__ import annotations
from hashlib import sha256
import argparse
import json
import os
import sys
import zlib

from run_lean_world_stream_pg import SCHEMA_RE
from lean_world_native_p1_pg import (
    retrieve_original_native_p1,bounded_original_alpha_fibre)

def analyze_original(conn,*,repository,revision,path,declaration,
                     export_sha256,top_k=25):
    original=retrieve_original_native_p1(
        conn,repository=repository,revision=revision,path=path,
        declaration=declaration,export_sha256=export_sha256)
    candidates=bounded_original_alpha_fibre(
        conn,toolchain=original["toolchain"],
        alpha_type=original["type_alpha"],limit=top_k)
    t=original["type_exact"]
    p=original["proof_exact"]
    source=original["source"]
    type_packed=zlib.compress(t,9)
    proof_packed=zlib.compress(p,9) if p else b""
    # These are direct physical baseline measurements, not global codec wins.
    return {
        "schema":"dashi-lean-p1-common-consumer-probe-v1",
        "status":"original-exporter-expr-candidate-only",
        "repository":repository,"revision":revision,
        "path":path,"declaration":declaration,
        "toolchain":original["toolchain"],
        "codec_sha256":original["p1_codec_sha256"],
        "source_sha256":sha256(source).hexdigest(),
        "type_exact_sha256":sha256(t).hexdigest(),
        "type_alpha_sha256":sha256(original["type_alpha"]).hexdigest(),
        "proof_exact_sha256":sha256(p).hexdigest() if p else None,
        "search":{
            "top_k":top_k,"returned":candidates["returned"],
            "complete":candidates["complete"],
            "more_possible":candidates["more_possible"],
            "next_keyset":[*candidates["next_keyset"][:4],
                           candidates["next_keyset"][4].hex()]
                     if candidates["next_keyset"] else None,
            "candidates":candidates["matches"],
            "fibre_is_not_semantic_equality":True
        },
        "compression_baseline":{
            "exact_type_bytes":len(t),
            "zlib9_exact_type_bytes":len(type_packed),
            "exact_proof_bytes":len(p),
            "zlib9_exact_proof_bytes":len(proof_packed),
            "same_original_object_used_by_fibre_and_MDL":True,
            "program_dictionary_bytes_counted":False,
            "fractions_discovered":False,
            "full_typed_MDL_win_claimed":False
        },
        "original_source_reconstructed_by_export_codec":False,
        "original_source_byte_store_verified":True,
        "kernel_certified":False,"world_admitted":False
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ("schema","repository","revision","path","declaration",
                "export-sha256"):
        p.add_argument("--"+key,required=True)
    p.add_argument("--top-k",type=int,default=25)
    a=p.parse_args()
    if not SCHEMA_RE.fullmatch(a.schema) or a.schema=="public":
        p.error("explicit nonpublic existing source schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("PGDATABASE must be explicit")
    try:
        import psycopg
        from psycopg import sql
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(a.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=a.schema:
                    raise ValueError("source-world schema missing")
            conn.commit()
            report=analyze_original(
                conn,repository=a.repository,revision=a.revision,
                path=a.path,declaration=a.declaration,
                export_sha256=a.export_sha256,top_k=a.top_k)
        print(json.dumps(report,sort_keys=True))
        return 0
    except (ValueError,OSError,ImportError) as exc:
        print("COMMON_P1_CONSUMER_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
