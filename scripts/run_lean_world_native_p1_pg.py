#!/usr/bin/env python3
"""Original native-v3 P1 exporter observation -> existing PostgreSQL source world.

No second world builder, no independent checker, no CI and no promotion.
Supply the actual #1495 codec module from an isolated local worktree.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
import os
import sys

from lean_world_native_p1_pg import (
    NativeP1PGError,load_selected_codec,persist_original_p1)
from run_lean_world_stream_pg import SCHEMA_RE

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--observation",required=True,type=Path)
    p.add_argument("--p1-codec",required=True,type=Path,
                   help="absolute path to #1495 scripts/lean_world_native_p1_codec.py")
    p.add_argument("--schema",required=True)
    p.add_argument("--jmd-builder-source",type=Path)
    p.add_argument("--native-export",type=Path)
    p.add_argument("--acknowledge-candidate-only",action="store_true")
    a=p.parse_args()
    if not SCHEMA_RE.fullmatch(a.schema) or a.schema=="public":
        p.error("explicit isolated original PostgreSQL source schema required")
    if not a.acknowledge_candidate_only:
        p.error("P1 observation is not a kernel-checked world theorem")
    if not os.environ.get("PGDATABASE"):
        p.error("PGDATABASE must be explicit")
    try:
        import psycopg
        from psycopg import sql
        codec=load_selected_codec(a.p1_codec)
        if (a.jmd_builder_source is None)!=(a.native_export is None):
            raise NativeP1PGError(
                "original JMD builder and native export must be supplied together")
        builder_evidence=None
        if a.jmd_builder_source is not None:
            from lean_world_native_p1_pg import inspect_observation
            from lean_world_jmd_native_owner_readonly import read_only_check
            observation,_,_,_,_=inspect_observation(a.observation,codec)
            builder_evidence=read_only_check(
                source_path=a.jmd_builder_source,
                export_path=a.native_export,
                declaration=observation["declaration"],
                expected_export_sha=observation["artifact_sha256"])
            from_native=lambda field: set(observation[field])
            # Reference owners use the original textual constant names;
            # both are candidate observations, never proof transports.
            if (set(builder_evidence["direct_type_constants"])-
                  {observation["declaration"]} !=
                    from_native("direct_statement_constants") or
                set(builder_evidence["direct_proof_constants"])-
                  {observation["declaration"]} !=
                    from_native("direct_proof_constants")):
                raise NativeP1PGError("independent original JMD parser disagrees about type/proof constant refs")
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(a.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=a.schema:
                    raise NativeP1PGError("original SQL source schema missing")
            conn.commit()
            result=persist_original_p1(conn,a.observation,codec)
        if builder_evidence is not None:
            result["jmd_original_builder_readonly"]=builder_evidence
        print(json.dumps(result,sort_keys=True))
        return 0
    except (ValueError,OSError,ImportError,KeyError) as exc:
        print("NATIVE_P1_PG_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
