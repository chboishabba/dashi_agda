#!/usr/bin/env python3
"""Ingest proof-aware agda2lean PR #9 capability receipts into DASHI's world DB.

agda2lean is Agda -> Lean, not Lean corpus ingestion. Its catalog gives the
mapping status of an existing Agda owner. This bridge reads that capability
without interpreting 'exact' or 'encoded' as a checked Lean proof. It requires
byte-identical checked Agda input and the canonical native index file receipt.
No LLM, new source index, network request, publication or auto agent involved.
"""
from __future__ import annotations
import argparse
import json
import re
import sqlite3
import subprocess
from pathlib import Path

MODES={"exact","encoded","reconstruct","quarantined","unsupported"}
FIELDS={"declaration","module","role","mapping_mode","object_hash",
        "checked_source_sha256","source_file","source_start_line",
        "source_end_line","authority","establishes_proof"}
SHA256=re.compile(r"[a-fA-F0-9]{64}\Z")


def parse_tsv(text: str) -> dict:
    fields={}
    deps=[]
    for line in text.splitlines():
        cells=line.split("\t")
        if len(cells)!=2:
            raise ValueError("Invalid capability TSV row")
        key,value=cells
        if key=="dependency":
            if not value: raise ValueError("Empty dependency")
            deps.append(value)
        elif key in FIELDS and key not in fields:
            fields[key]=value
        else:
            raise ValueError(f"Unexpected or duplicate capability field: {key}")
    if set(fields)!=FIELDS:
        raise ValueError(f"Missing capability keys: {FIELDS-set(fields)}")
    if fields["mapping_mode"] not in MODES:
        raise ValueError("Unknown agda2lean mapping mode")
    if fields["authority"]!="translation-capability-only" or fields["establishes_proof"]!="false":
        raise ValueError("Capability illegally asserts proof authority")
    if not SHA256.fullmatch(fields["checked_source_sha256"]):
        raise ValueError("Missing valid checked Agda source hash")
    if not fields["object_hash"] or not fields["declaration"] or not fields["module"]:
        raise ValueError("Empty source identifier")
    for key in ("source_start_line","source_end_line"):
        fields[key]=int(fields[key])
    if fields["source_start_line"]<=0 or fields["source_end_line"]<fields["source_start_line"]:
        raise ValueError("Invalid source range")
    fields["dependencies"]=sorted(set(deps))
    return fields


def verify_source(conn: sqlite3.Connection, capability: dict) -> bool:
    """Compare checked source bytes with dashi-repo's canonical indexed file."""
    row=conn.execute("""SELECT s.module,s.file,f.sha256
       FROM repo_symbols s JOIN repo_files f ON f.path=s.file
       WHERE s.symbol_id=? AND s.language='agda'""",
       (capability["declaration"],)).fetchone()
    return bool(row and
        row[0]==capability["module"] and
        row[1]==capability["source_file"] and
        row[2].lower()==capability["checked_source_sha256"].lower())


def ingest(conn: sqlite3.Connection, capability: dict) -> bool:
    ready=verify_source(conn,capability)
    conn.execute("""INSERT INTO jmd_world_a2l_capabilities
       VALUES(?,?,?,?,?,?,?,?,?,'translation-capability-only',0)
       ON CONFLICT(declaration) DO UPDATE SET
         module=excluded.module,mode=excluded.mode,
         object_hash=excluded.object_hash,
         checked_source_sha256=excluded.checked_source_sha256,
         source_file=excluded.source_file,
         source_start_line=excluded.source_start_line,
         source_end_line=excluded.source_end_line,
         current_source_matches=excluded.current_source_matches,
         authority=excluded.authority,
         establishes_proof=excluded.establishes_proof""",
       (capability["declaration"],capability["module"],capability["mapping_mode"],
        capability["object_hash"],capability["checked_source_sha256"],
        capability["source_file"],capability["source_start_line"],
        capability["source_end_line"],int(ready)))
    conn.execute("DELETE FROM jmd_world_a2l_dependencies WHERE declaration=?",
                 (capability["declaration"],))
    for dep in capability["dependencies"]:
        conn.execute("INSERT INTO jmd_world_a2l_dependencies VALUES(?,?)",
                     (capability["declaration"],dep))
    return ready


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--a2l-catalog",required=True,type=Path)
    p.add_argument("--a2l-binary",default="agda2lean-capability")
    p.add_argument("--declarations",required=True,type=Path,
                   help="File with fully qualified indexed Agda owner names, one per line")
    args=p.parse_args(argv)
    if not args.database.is_file() or not args.a2l_catalog.is_file():
        p.error("Missing existing canonical DB or agda2lean catalog")
    from jmd_formal_world_reconcile import init
    conn=sqlite3.connect(args.database)
    try:
        init(conn)
        names=sorted(set(x.strip() for x in
                    args.declarations.read_text(encoding="utf-8").splitlines() if x.strip()))
        passed=stale=0
        with conn:
            for name in names:
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",name):
                    raise ValueError("Bad Agda declaration name")
                proc=subprocess.run([args.a2l_binary,"--database",
                   str(args.a2l_catalog),"--declaration",name],
                   capture_output=True,text=True,timeout=45,check=False)
                if proc.returncode:
                    raise ValueError(f"agda2lean capability failure {name}: {proc.stderr[:500]}")
                capability=parse_tsv(proc.stdout)
                if capability["declaration"]!=name:
                    raise ValueError("agda2lean queried declaration differs from output")
                if ingest(conn,capability): passed+=1
                else: stale+=1
        print(json.dumps({"schema":"jmd-a2l-join-v1",
                          "capability_declarations":len(names),
                          "source_fresh":passed,"source_stale_or_missing":stale,
                          "lean_kernel_proofs":0,
                          "agda_kernel_proofs":0,
                          "authority":"translation-capability-only"},indent=2))
    finally:
        conn.close()


if __name__=="__main__":
    main()
